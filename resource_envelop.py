import igraph

class SimpleTemporalProblemInstance:

	def __init__(self):
		self.nodes = dict()
		self.g = igraph.Graph(directed=True, edge_attrs={"weight": 1})
		self.g.add_vertex()
		self._shortest_paths = None
		self._modified = True

	def add_node(self, name, **kwargs):
		if name not in self.nodes:
			self._modified = True
			vid = self.g.vcount()
			self.nodes[name] = vid
			self.g.add_vertex(name)
			for key, value in kwargs.iteritems():
				self.g.vs[vid][key] = value
			return name

	def add_constraint(self, event0, event1, up_bound=None, lower_bound=None):
		if up_bound != None:
			self._modified = True
			self.g.add_edge(event0, event1, weight=up_bound)
		if lower_bound != None:
			self._modified = True
			self.g.add_edge(event1, event0, weight=-lower_bound)

	def shortest_paths(self):
		if self._modified:
			self._modified = False
			try:
				self._shortest_paths = tuple(tuple(x) for x in self.g.shortest_paths_dijkstra(weights="weight"))
			except igraph._igraph.InternalError:
				return None
		return self._shortest_paths

	def shortest_path_pair(self, node0, node1):
		vid0 = self.nodes[node0]
		vid1 = self.nodes[node1]
		return self.shortest_paths()[vid0][vid1]

	def test_consistency(self):
		return True if self.shortest_paths() else False


class ResourceEnvelopSolver:

	def __init__(self, stp):
		self.stp = stp

	def _build_bipartite_graph(stp):
		g = igraph.Graph(directed=True, edge_attrs={"weight": 1})
		g.add_vertex()
		source = g.vs[0]
		g.add_vertex()
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

	def _create_timeline(stp):
		timeline = list(enumerate(stp.shortest_paths()[0]))
		timeline.sort(key=lambda tup: tup[1])
		return timeline[1:]

	def solve(self):
		g, producers, consumers = _build_bipartite_graph(self.stp)
		vertices = consumers

		max_production = list()

		for vid, t in _create_timeline(self.stp):
			#Remove Nodes
			if self.stp.vs[vid]["production"] < 0:
				vertices.remove(vid)
			elif self.stp.vs[vid]["production"] > 0:
				vertices.add(vid)

			g_temp = g.subgraph(list(vertices))
			source = g_temp.vs[0]
			target = g_temp.vs[1]

			mf = g_temp.maxflow(0, 1).value

			# max_indenpendent_set = set()
			max_production_t = 0

			for p in source.successors():
				eid = g_temp.get_eid(s, p)
				if p["production"] == mf.flow[eid]:
					# max_indenpendent_set.add(p)
					max_production_t += p["production"]
			for c in target.predecessors():
				eid = g_temp.get_eid(s, c)
				if c["production"] != mf.flow[eid]:
					# max_indenpendent_set.add(c)
					max_production_t += c["production"]

			max_production.append((t, max_production_t))

		return max_production
			





