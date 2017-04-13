from __future__ import print_function
import igraph
import math, copy
import matplotlib.pyplot as plt
import numpy
from gurobipy import Model, GurobiError, GRB
from operator import mul



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
        """Adds a new constraint.

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


class ResourceEnvelopeSolver:
    """The solver class to solve the resource envelope problem. For the details of the approach, please refer to
    T. K. Satish Kumar (2003). Incremental Computation of Resource-Envelopes in Producer-Consumer Models.
    Proceedings of the Ninth International Conference on Principles and Practice of Constraint Programming (CP-2003).
    """

    def __init__(self, stp):
        """Initializes the solver instance.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        """
        self.stp = stp
        self.bi = self._build_bipartite_graph(stp)
        self.timeline = list(self._create_timeline(stp))
        stp_inverse = copy.copy(stp)
        for v in stp_inverse.g.vs:
            for key, value in v.attributes().iteritems():
                if key != "name" and value is not None:
                    v[key] = -value
        self.bi_inverse = self._build_bipartite_graph(stp_inverse)
        self.timeline_inverse = list(self._create_timeline(stp_inverse))

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
                if stp.shortest_path_pair(g.vs[p]["name"], g.vs[c]["name"]) < 0:
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

    def solve(self, key, lower_bounds):

        """Solves the resource envelope problem.

        @return: the resource envelope. It is two list of tuples. Each tuple consists of a time step and the maximum/minimum production thereof.
        """
        return self.upper(key, lower_bounds), self.lower(key, lower_bounds)

    def upper(self, key, lower_bounds, isupper=True):

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
        max_production = list()
        max_production_0 = 0
        bound_index = 0
        for t, vids in timeline:
            for vid in vids:
                if g.vs[vid-1][key] < 0:
                    max_production_0 += g.vs[vid-1][key]
                    vertices.remove(vid-1)
                elif g.vs[vid-1][key] > 0:
                    vertices.add(vid-1)
            
            g_temp = g.subgraph(list(vertices))

            # Compute the maximum weighted independent set.
            try:
                # Create a new model
                m = Model()
                m.NumObj = 2
                variables = m.addVars(range(len(g_temp.vs)), vtype=GRB.CONTINUOUS, ub=1.0, lb=0.0)
                for e in g_temp.es:
                    m.addConstr(variables[e.source]+variables[e.target] <= 1)
                m.ModelSense = GRB.MAXIMIZE
                m.setParam(GRB.Param.ObjNumber, 0)
                m.ObjNPriority = 1
                m.setAttr(GRB.Attr.ObjN, variables, map(abs, g_temp.vs[key]))

                m.ModelSense = GRB.MAXIMIZE
                m.setParam(GRB.Param.ObjNumber, 1)
                m.ObjNPriority = 0
                m.setAttr(GRB.Attr.ObjN, variables, [self.stp.shortest_path_pair("x0", x) + self.stp.shortest_path_pair(x, "x0") for x in g_temp.vs["name"]])

                m.optimize()
                for v in m.getVars():
                    print('%s %g' % (v.varName, v.x))

                print('Obj: %g' % m.objVal)
                max_production_t = max_production_0
                for vid, x in enumerate(m.getVars()):
                    if (x.x > 0.99 and g_temp.vs[vid][key] > 0) or (x.x < 0.01 and g_temp.vs[vid][key] < 0):
                        max_production_t += g_temp.vs[vid][key]
            except GurobiError as e:
                print('Error code ' + str(e.errno) + ": " + str(e))
            
            max_production.append((t, max_production_t))

        return max_production

    def lower(self, key, lower_bounds):

        """Solves the resource envelope lower bound.

        @return: the resource envelope. It is a list of tuples. Each tuple consists of a time step and the minimum production thereof.
        """

        result = list()
        for t in self.upper(key, lower_bounds, False):
            result.append((t[0], -t[1]))
        return result

if __name__ == '__main__':
    stp = SimpleTemporalProblemInstance()
    x1 = stp.add_node("x1", production=1, weapon=0, fuel=50)
    x2 = stp.add_node("x2", production=-1, weapon=-5, fuel=-50)
    x3 = stp.add_node("x3", production=1, weapon=10, fuel=150)
    x4 = stp.add_node("x4", production=1, weapon=2, fuel=250)

    stp.add_constraint(stp.g.vs[0], x1, 5, 10)
    stp.add_constraint(stp.g.vs[0], x3, 10, 10)
    stp.add_constraint(x1, x2, 5, 8)
    stp.add_constraint(x2, x4, 2, 4)
    stp.add_constraint(x3, x4, 5, 10)
    r = ResourceEnvelopeSolver(stp)
    envelope = r.solve("fuel", [])
    print (envelope)

    x1 = [0] + [i[0] for i in envelope[0]] + [30.0]
    y1 = [0] + [i[1] for i in envelope[0]] + [envelope[0][-1][1]]
    x2 = [0] + [i[0] for i in envelope[1]] + [30.0]
    y2 = [0] + [i[1] for i in envelope[1]] + [envelope[1][-1][1]]
    plt.clf()
    plt.step(x1, y1, where='post')
    plt.step(x2, y2, where='post')

    # envelope = r.solve("weapon", [])

    # x1 = [0] + [i[0] for i in envelope[0]] + [30.0]
    # y1 = [0] + [i[1] for i in envelope[0]] + [envelope[0][-1][1]]
    # x2 = [0] + [i[0] for i in envelope[1]] + [30.0]
    # y2 = [0] + [i[1] for i in envelope[1]] + [envelope[1][-1][1]]

    # plt.step(x1, y1, where='post')
    # plt.step(x2, y2, where='post')

    plt.ylabel('PRODUCTION')
    plt.xlabel('TIME')
    plt.xlim(0,30)
    plt.show()
