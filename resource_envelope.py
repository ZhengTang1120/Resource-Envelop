from __future__ import print_function
import igraph
import math, copy
import numpy
from gurobipy import Model, GurobiError, GRB
from operator import mul
import itertools
import sys



class SimpleTemporalProblemInstance:
    "Describes a simple temporal problem instance."

    def __init__(self, x0="x0"):
        """Initializes a SimpleTemporalProblemInstance object.

        @param x0: name of the x0 event node.
        """

        #All nodes in this graph in dict: {node name: node id}
        self.nodes = dict(x0=0)
        self.x0 = x0
        self.g = igraph.Graph(directed=True, edge_attrs={"weight": 1})
        #Add x null
        self.g.add_vertex(x0)
        #All shortest paths between nodes in this graph
        self._shortest_paths = None
        #Every time if the graph is changed, this is set to True. This is for the lazy call of the function shortest_paths().
        self._modified = True

    def add_node(self, name, **kwargs):
        """Adds a new event node.

        Keywords specify the attributes of the new node.

        @param name: name of the new node.
        @return: the name of the new node.
        """

        if name not in self.nodes:
            self._modified = True
            vid = self.g.vcount()
            self.nodes[name] = vid
            self.g.add_vertex(name)
            for key, value in kwargs.iteritems():
                self.g.vs[vid][key] = value
            return name

    def add_constraint(self, event0, event1, lower_bound=None, up_bound=None):
        """Adds a new constraint: lower_bound <= time of event1 - time of event0 <= up_bound

        @param event0: the first event in the constraint.
        @param event1: the second event in the constraint.
        @param lower_bound: the lower bound of the constraint.
        @param upper_bound: the upper bound of the constraint.
        """

        if up_bound is not None:
            self._modified = True
            self.g.add_edge(event0, event1, weight=up_bound)
        if lower_bound is not None:
            self._modified = True
            self.g.add_edge(event1, event0, weight=-lower_bound)

    def shortest_paths(self):
        """Computes the lengths of shortest paths for all vertices in the simple temporal graph.

        @return: a matrix that specifies the lengths of the shortest paths between vertices.
        """

        if self._modified:
            self._modified = False
            try:
                self._shortest_paths = tuple(tuple(x) for x in self.g.shortest_paths(weights="weight"))
            except igraph._igraph.InternalError:
                self._modified = True
                return None
        return self._shortest_paths

    def shortest_path_pair(self, node0, node1):
        """Computes the length of the shortest path between @node0 and @node1.

        @param node0: the name of the starting vertex of the shortest path.
        @param node1: the name of the ending vertex of the shortest path.
        @return: the length of the shortest path between @node0 and @node1.
        """

        vid0 = self.nodes[node0]
        vid1 = self.nodes[node1]
        return self.shortest_paths()[vid0][vid1]

    def test_consistency(self):
        """Tests whether there exists a solution for this simple temporal problem.

        THe consistency is tested by checking the exsitence of negative cycles.

        @return: C{True} if consistent. C{False} if inconsistent.
        """

        return True if self.shortest_paths() else False

    def reduce(self, nodes):
        """Reduces itself with only @nodes left."""

        removed_nodes = [item for item in self.g.vs["name"] if item not in nodes and item != "x0"]
        for node in removed_nodes:
            sp = self.shortest_paths()
            nid = self.nodes[node]
            adjacent_vs = set()
            for eid in self.g.incident(nid, mode=igraph.ALL):
                e = self.g.es[eid]
                adjacent_vs.add(e.source if e.source != nid else e.target)
            for av0, av1 in itertools.product(adjacent_vs, repeat=2):
                if av0 != av1:
                    self.add_constraint(av0, av1, up_bound=sp[av0][av1])
            self.g.delete_vertices(nid)
            for key in self.nodes:
                if self.nodes[key] > nid:
                    self.nodes[key] -= 1
        return self

    def create_subproblem(self, nodes):
        """Create a subproblem of @nodes."""

        return copy.deepcopy(self).reduce(nodes)


class ResourceEnvelopeSolver:
    """The solver class to solve the resource envelope problem. For the details of the approach, please refer to
    T. K. Satish Kumar (2003). Incremental Computation of Resource-Envelopes in Producer-Consumer Models.
    Proceedings of the Ninth International Conference on Principles and Practice of Constraint Programming (CP-2003).
    """

    def __init__(self, stp):
        """Initializes the solver instance.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        """
        self.stp = copy.deepcopy(stp)
        self.bi = self._build_bipartite_graph(stp)
        self.timeline = list(self._create_timeline(stp))
        stp_inverse = self._inverse_stp()
        self.bi_inverse = self._build_bipartite_graph(stp_inverse)
        self.timeline_inverse = list(self._create_timeline(stp_inverse))

    def _inverse_stp(self):
        """Inverses self.stp by negating all attributes of each node.

        @return the inversed stp.
        """

        stp_inverse = copy.deepcopy(self.stp)
        for v in stp_inverse.g.vs:
            for key, value in v.attributes().iteritems():
                if key != "name" and value is not None:
                    v[key] = -value
        return stp_inverse

    def _build_bipartite_graph(self, stp):
        """Builds a bipartite graph. The bipartite graph is necessary as an immediate step to solve the resource envelop problem.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        @return: the bipartite graph.
        """

        g = igraph.Graph()
        producers = set()
        consumers = set()
        for i, vertex in enumerate(stp.g.vs[1:]):
            g.add_vertex(vertex["name"])
            v = g.vs[i]
            for key, value in vertex.attributes().iteritems():
                v[key] = value
            
            if v["production"] > 0:
                producers.add(v.index)
            elif v["production"] < 0:
                consumers.add(v.index)

        for p in producers:
            for c in consumers:
                if stp.shortest_path_pair(g.vs[p]["name"], g.vs[c]["name"]) <= 0:
                    g.add_edge(p, c)

        return g, producers, consumers

    def _create_timeline(self, stp):
        """Computes the time steps at which the production of the resource envelop may change.

        This function is a generator which generates a tuple each time.
        The first element of the tuple is the time step, and the second element of the tuple is a list of vids.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        """

        timeline = [None for _ in xrange(1, len(stp.g.vs))]
        for i in xrange(1, len(stp.g.vs)):
            v = stp.g.vs[i]
            if v["production"] > 0:
                timeline[i-1] = (-stp.shortest_path_pair(v["name"], stp.x0), i)
            elif v["production"] < 0:
                timeline[i-1] = (stp.shortest_path_pair(stp.x0, v["name"]), i)
                
        timeline.sort(key=lambda tup: tup[0])
        last_t = None
        vid_list = []
        for t in timeline:
            if last_t is not None and t[0] != last_t:
                yield (last_t, vid_list)
                vid_list = []
            vid_list.append(t[1])
            last_t = t[0]

        if last_t is not None:
            yield (last_t, vid_list)

    def solve(self, key, lower_bound=None):
        """Solves the resource envelope problem.

        @return: the resource envelope. It is two list of tuples. Each tuple consists of a time step and the maximum/minimum production thereof.
        """
        if lower_bound is not None:
            g = self.bi_inverse[0]
            producers = self.bi_inverse[1].copy()
            consumers = self.bi_inverse[2].copy()
            timeline = self.timeline_inverse
            max_production_0 = 0
            vertices = list()
            for v in producers|consumers:
                if (lower_bound[1] >= -self.stp.shortest_path_pair(g.vs[v]["name"], "x0") and
                    lower_bound[0] <= self.stp.shortest_path_pair("x0", g.vs[v]["name"])):
                    vertices.append(v)
                elif self.stp.shortest_path_pair("x0", g.vs[v]["name"])< lower_bound[0]:
                    max_production_0 += g.vs[v][key]


            g_temp = g.subgraph(vertices)
            print (max_production_0)

            for vid, x in enumerate(self._upper_t(g_temp, key, -lower_bound[2]-max_production_0)):
                if x > 1e-6 and g_temp.vs[vid][key] < 0:
                    self.stp.add_constraint(self.stp.g.vs[0], g_temp.vs[vid]["name"], up_bound=lower_bound[0])
                elif (x < 1-1e-6 and g_temp.vs[vid][key] > 0):
                    self.stp.add_constraint(self.stp.g.vs[0], g_temp.vs[vid]["name"], lower_bound=lower_bound[1])

            self.bi = self._build_bipartite_graph(self.stp)
            self.timeline = list(self._create_timeline(self.stp))
            stp_inverse = self._inverse_stp()
            
            self.bi_inverse = self._build_bipartite_graph(stp_inverse)
            self.timeline_inverse = list(self._create_timeline(stp_inverse))

        return self.upper(key), self.lower(key)

    def upper(self, key, isupper=True):
        """Solves the resource envelope upper bound.

        @return: the resource envelope. It is a list of tuples. Each tuple consists of a time step and the maximum production thereof.
        """

        if isupper:
            g = self.bi[0]
            producers = self.bi[1].copy()
            consumers = self.bi[2].copy()
            timeline = self.timeline
        else:
            g = self.bi_inverse[0]
            producers = self.bi_inverse[1].copy()
            consumers = self.bi_inverse[2].copy()
            timeline = self.timeline_inverse

        vertices = consumers
        print(vertices)
        max_production = list()
        max_production_0 = 0
        bound_index = 0
        for t, vids in timeline:
            for vid in vids:
                if g.vs[vid-1][key] < 0:
                    max_production_0 += g.vs[vid-1][key]
                    print ("vid", vid)
                    vertices.remove(vid-1)
                elif g.vs[vid-1][key] > 0:
                    vertices.add(vid-1)
                
            g_temp = g.subgraph(list(vertices))
                
            max_production_t = max_production_0
            for vid, x in enumerate(self._upper_t(g_temp, key)):
                if (x > 0.99 and g_temp.vs[vid][key] > 0) or (x < 0.01 and g_temp.vs[vid][key] < 0):
                    max_production_t += g_temp.vs[vid][key]
            max_production.append((t, max_production_t))


        return max_production

    def lower(self, key):
        """Solves the resource envelope lower bound.

        @return: the resource envelope. It is a list of tuples. Each tuple consists of a time step and the minimum production thereof.
        """

        result = list()
        for t in self.upper(key, False):
            result.append((t[0], -t[1]))
        return result

    def _upper_t(self, g, key, lower=None):
        """Solves the uppper bound at time t.

        @param g: subgraph of bipartite graph at time t. 
        @param key: the resource name.
        @return: the uppper bound at t.
        """
        print(lower)
        # Compute the maximum weighted independent set.
        try:
            # Create a new model
            m = Model()
            m.NumObj = 2
            variables = m.addVars(range(len(g.vs)), vtype=GRB.CONTINUOUS, ub=1.0, lb=0.0)
            for e in g.es:
                m.addConstr(variables[e.source]+variables[e.target] <= 1)
            if lower is not None:
                m.addConstr(sum(variables[v] * g.vs[v][key] for v in xrange(len(g.vs))) <= lower)
            m.ModelSense = GRB.MAXIMIZE
            m.setParam(GRB.Param.ObjNumber, 0)
            m.ObjNPriority = 1
            m.setAttr(GRB.Attr.ObjN, variables, map(abs, g.vs[key]))

            m.ModelSense = GRB.MAXIMIZE
            m.setParam(GRB.Param.ObjNumber, 1)
            m.ObjNPriority = 0
            m.setAttr(GRB.Attr.ObjN, variables, [-self.stp.shortest_path_pair("x0", x) - self.stp.shortest_path_pair(x, "x0") for x in g.vs["name"]])

            m.optimize()
            for v in m.getVars():
                print('%s %g' % (v.varName, v.x))

            print('Obj: %g' % m.objVal)
            
            return [x.x for x in m.getVars()]
        except GurobiError as e:
            print('Error code ' + str(e.errno) + ": " + str(e))

def run(j):
    if j["constraint"] != []:
        constraint = j["constraint"][1:]
    else:
        constraint = None
    print (constraint)
    stp = SimpleTemporalProblemInstance()
    x = dict()
    nodes = j["nodes"]
    for node in nodes:
        if eval(node["title"])["name"] != "x0":
            x[node["id"]] = stp.add_node(**eval(node["title"]))
        else:
            x[node["id"]] = "x0"
    edges = j["edges"]
    for edge in edges:
        stp.add_constraint(x[edge["source"]["id"]], x[edge["target"]["id"]], eval(edge["title"])[0], eval(edge["title"])[1])
    
    r = ResourceEnvelopeSolver(stp)
    envelope = r.solve("production")
    for c in constraint:
        envelope = r.solve("production", c)
    if len(envelope[0]) == 0 or len(envelope[1]) == 0:
        return [['x1'], ['data1'], ['x2'], ['data2']]
    x1 = ['x1',0] + [i[0] for i in envelope[0]] + [30.0]
    y1 = ['production_upper1',0] + [i[1] for i in envelope[0]] + [envelope[0][-1][1]]
    x2 = ['x2',0] + [i[0] for i in envelope[1]] + [30.0]
    y2 = ['production_lower1',0] + [i[1] for i in envelope[1]] + [envelope[1][-1][1]]

    # titles = dict()
    # for e in r.stp.g.es:
    #     k = r.stp.g.vs[e.source]["name"]+r.stp.g.vs[e.target]["name"] if r.stp.g.vs[e.source]["name"] > r.stp.g.vs[e.target]["name"] else r.stp.g.vs[e.target]["name"]+r.stp.g.vs[e.source]["name"]
    #     if (k) not in titles:
    #         titles[(k)] = [None, None]
    #         if e["weight"] >= 0:
    #             titles[(k)][1] = e["weight"]
    #         else:
    #             titles[(k)][0] = -e["weight"]
    #     else:
    #         if e["weight"] >= 0 and titles[(k)][1] is None:
    #             titles[(k)][1] = e["weight"]
    #         if e["weight"] >= 0 and titles[(k)][1] is not None:
    #             if e["weight"] < titles[(k)][1]:
    #                 titles[(k)][1] = e["weight"]
    #         if e["weight"] < 0 and titles[(k)][0] is None:
    #             titles[(k)][0] = -e["weight"]
    #         if e["weight"] < 0 and titles[(k)][0] is not None:
    #             if e["weight"] > titles[(k)][0]:
    #                 titles[(k)][0] = -e["weight"]
    # print(titles)

    # for edge in j["edges"]:
    #     k = x[edge["source"]["id"]]+x[edge["target"]["id"]] if x[edge["source"]["id"]]>x[edge["target"]["id"]] else x[edge["target"]["id"]]+x[edge["source"]["id"]]
    #     edge["title"] = str(titles[k])
    if constraint:
        li = [x1, y1, x2, y2]
        for i,c in enumerate(constraint):
            xc = ['xc_'+str(i)] + c[:2]
            yc = ['lower_bound_'+str(i)] + [c[2], c[2]]
            li += [xc, yc]
        print (li)
        return li, j
    else:
        return [x1, y1, x2, y2], j



