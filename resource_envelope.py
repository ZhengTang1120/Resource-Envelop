from __future__ import print_function
import igraph
import math, copy
import matplotlib.pyplot as plt



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

    def _build_bipartite_graph(self, stp):
        """Builds a bipartite graph. The bipartite graph is necessary as an immediate step to solve the resource envelop problem.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        @return: the bipartite graph.
        """

        g = igraph.Graph(directed=True, edge_attrs={"weight": 1})
        g.add_vertex("source")
        source = g.vs[0]
        g.add_vertex("target")
        target = g.vs[1]
        producers = set()
        consumers = set()
        for i, vertex in enumerate(stp.g.vs[1:], 2):
            g.add_vertex(vertex["name"], production=vertex["production"])
            v = g.vs[i]
            if v["production"] > 0:
                g.add_edge(source, v, capacity=abs(v["production"]))
                producers.add(v)
            elif v["production"] < 0:
                g.add_edge(v, target, capacity=abs(v["production"]))
                consumers.add(v)

        for p in producers:
            for c in consumers:
                if stp.shortest_path_pair(p["name"], c["name"]) < 0:
                    g.add_edge(p, c, capacity=float("inf"))

        return g, producers, consumers

    def _create_timeline(self,stp):
        """Computes the time steps at which the production of the resource envelop may change.

        This function is a generator which generates a tuple each time.
        The first element of the tuple is the time step, and the second element of the tuple is a list of vids.

        @param stp: the L{SimpleTemporalProblemInstance} object that specifies the simple temporal problem.
        """

        timeline = [None for i in xrange(1, len(stp.g.vs))]
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

    def solve(self):

        """Solves the resource envelope problem.

        @return: the resource envelope. It is two list of tuples. Each tuple consists of a time step and the maximum/minimum production thereof.
        """

        return self.upper(self.stp), self.lower()

    def upper(self, stp):

        """Solves the resource envelope upper bound.

        @return: the resource envelope. It is a list of tuples. Each tuple consists of a time step and the maximum production thereof.
        """

        g, producers, consumers = self._build_bipartite_graph(stp)
        vertices = consumers
        vertices.add(g.vs[0])
        vertices.add(g.vs[1])
        max_production = list()
        max_production_0 = 0
        for t, vids in self._create_timeline(stp):
            for vid in vids:
                if stp.g.vs[vid]["production"] < 0:
                    max_production_0 += g.vs[vid+1]["production"]
                    vertices.remove(g.vs[vid+1])
                elif stp.g.vs[vid]["production"] > 0:
                    vertices.add(g.vs[vid+1])
            
            g_temp = g.subgraph(list(vertices))

            # Compute the maximum weighted independent set according to Figure 4.
            mf = g_temp.maxflow(0, 1)
            residual_graph = igraph.Graph(len(g_temp.vs), directed=True)
            for i, edge in enumerate(g_temp.es):
                if (edge["capacity"] - mf.flow[i]) / edge["capacity"] > 1e-10:
                    residual_graph.add_edge(edge.source, edge.target)
                elif mf.flow[i] > 1e-10:
                    residual_graph.add_edge(edge.target, edge.source)

            max_production_t = max_production_0
            for v in residual_graph.subcomponent(0, mode=igraph.OUT):
                if v > 1:
                    max_production_t += g_temp.vs[v]["production"]

            max_production.append((t, max_production_t))

        return max_production

    def lower(self):

        """Solves the resource envelope lower bound.

        @return: the resource envelope. It is a list of tuples. Each tuple consists of a time step and the minimum production thereof.
        """

        stp_l = copy.deepcopy(self.stp)
        for v in stp_l.g.vs:
            if v["production"] is not None:
                v["production"] = -v["production"]
        result = list()
        for t in self.upper(stp_l):
            result.append((t[0], -t[1]))
        return result

def test1():
    stp = SimpleTemporalProblemInstance()
    x1 = stp.add_node("x1", production=5)
    x2 = stp.add_node("x2", production=-5)
    x3 = stp.add_node("x3", production=15)
    x4 = stp.add_node("x4", production=2)

    stp.add_constraint(stp.g.vs[0], x1, 5, 10)
    stp.add_constraint(stp.g.vs[0], x3, 30, 30)
    stp.add_constraint(x1, x2, 20, 20)
    stp.add_constraint(x2, x3, 5, 10)
    stp.add_constraint(x3, x4, 2, 2)

    r = ResourceEnvelopeSolver(stp)
    print(r.solve())
    print("Test1: {}".format(r.solve()[0] == [(5.0, 5), (25.0, 0), (30.0, 15), (32.0, 17)]))

def test2():
    stp = SimpleTemporalProblemInstance()
    x1 = stp.add_node("x1", production=10)
    x2 = stp.add_node("x2", production=-1)
    x3 = stp.add_node("x3", production=100)
    x4 = stp.add_node("x4", production=1000)

    stp.add_constraint(stp.g.vs[0], x1, 5, 10)
    stp.add_constraint(stp.g.vs[0], x3, 10, 10)
    stp.add_constraint(x1, x2, 5, 8)
    stp.add_constraint(x2, x4, 2, 4)
    stp.add_constraint(x3, x4, 5, 11)

    r = ResourceEnvelopeSolver(stp)
    print(r.solve())
    print("Test2: {}".format(r.solve()[0] == [(5.0, 10), (10.0, 110), (15.0, 1110), (18.0, 1109)]))

if __name__ == '__main__':
    stp = SimpleTemporalProblemInstance()
    x1 = stp.add_node("x1", production=10)
    x2 = stp.add_node("x2", production=-10)
    x3 = stp.add_node("x3", production=100)
    x4 = stp.add_node("x4", production=200)

    stp.add_constraint(stp.g.vs[0], x1, 5, 10)
    stp.add_constraint(stp.g.vs[0], x3, 10, 10)
    stp.add_constraint(x1, x2, 5, 8)
    stp.add_constraint(x2, x4, 2, 4)
    stp.add_constraint(x3, x4, 5, 11)
    r = ResourceEnvelopeSolver(stp)
    envelope = r.solve()

    x1 = [0] + [i[0] for i in envelope[0]] + [30.0]
    y1 = [0] + [i[1] for i in envelope[0]] + [envelope[0][-1][1]]
    x2 = [0] + [i[0] for i in envelope[1]] + [30.0]
    y2 = [0] + [i[1] for i in envelope[1]] + [envelope[1][-1][1]]

    plt.step(x1, y1, where='post')
    plt.step(x2, y2, where='post')
    plt.ylabel('PRODUCTION')
    plt.xlabel('TIME')
    plt.xlim(0,30)
    plt.show()