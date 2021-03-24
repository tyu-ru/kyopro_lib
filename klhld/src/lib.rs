pub struct HLD {
    root: usize,
    parent: Vec<usize>,
    depth: Vec<usize>,
    top: Vec<usize>,
    vertex_to_index: Vec<usize>,
    index_to_vertex: Vec<usize>,
}

impl HLD {
    pub fn new<T>(tree: &Vec<Vec<(usize, T)>>, root: usize) -> Self {
        let n = tree.len();
        let mut slf = Self {
            root,
            parent: vec![0; n],
            depth: vec![0; n],
            top: vec![0; n],
            vertex_to_index: vec![0; n],
            index_to_vertex: vec![],
        };
        slf.parent[root] = root;
        let mut max_size_child = vec![None; n];
        slf.dfs1(tree, &mut max_size_child, root, root);
        slf.dfs2(tree, &max_size_child, root, root, root);
        slf
    }

    fn dfs1<T>(
        &mut self,
        tree: &Vec<Vec<(usize, T)>>,
        max_size_child: &mut Vec<Option<usize>>,
        v: usize,
        p: usize,
    ) -> usize {
        self.parent[v] = p;
        self.depth[v] = self.depth[p] + 1;
        let mut s = 1;
        let mut max_child = None;
        for u in &tree[v] {
            let u = u.0;
            if u == p {
                continue;
            }
            let subtree_size = self.dfs1(tree, max_size_child, u, v);
            s += subtree_size;
            max_child = std::cmp::max(max_child, Some((subtree_size, u)));
        }
        max_size_child[v] = max_child.map(|(_, idx)| idx);
        s
    }

    fn dfs2<T>(
        &mut self,
        tree: &Vec<Vec<(usize, T)>>,
        max_size_child: &Vec<Option<usize>>,
        v: usize,
        p: usize,
        top_node: usize,
    ) -> Option<()> {
        self.top[v] = top_node;
        self.vertex_to_index[v] = self.index_to_vertex.len();
        self.index_to_vertex.push(v);
        let mx = max_size_child[v]?;
        self.dfs2(tree, max_size_child, mx, v, top_node);

        for u in &tree[v] {
            let u = u.0;
            if u == p || u == mx {
                continue;
            }
            self.dfs2(tree, max_size_child, u, v, u);
        }
        Some(())
    }

    pub fn to_hld_index(&self, node_index: usize) -> usize {
        self.vertex_to_index[node_index]
    }
    pub fn to_child_side_hld_index(&self, a: usize, b: usize) -> usize {
        self.to_hld_index(if self.depth[a] > self.depth[b] { a } else { b })
    }

    pub fn lca(&self, mut v: usize, mut u: usize) -> usize {
        while self.top[v] != self.top[u] {
            if self.depth[self.top[v]] > self.depth[self.top[u]] {
                std::mem::swap(&mut v, &mut u);
            }
            u = self.parent[self.top[u]];
        }
        if self.depth[v] < self.depth[u] {
            v
        } else {
            u
        }
    }

    fn path_query_impl<T, F1, F2>(
        &self,
        sequence_query: &F1,
        marge: &F2,
        mut v: usize,
        mut u: usize,
    ) -> (usize, usize, T)
    where
        T: Clone,
        F1: Fn(std::ops::RangeInclusive<usize>) -> T,
        F2: Fn(&T, &T) -> T,
    {
        if self.depth[v] > self.depth[u] {
            std::mem::swap(&mut v, &mut u);
        }
        let mut res = sequence_query(self.vertex_to_index[u]..=self.vertex_to_index[u]);
        if u == self.root {
            return (v, v, res);
        }
        u = self.parent[u];
        while self.top[v] != self.top[u] {
            if self.depth[self.top[v]] > self.depth[self.top[u]] {
                std::mem::swap(&mut v, &mut u);
            }
            let x = sequence_query(self.vertex_to_index[self.top[u]]..=self.vertex_to_index[u]);
            res = marge(&res, &x);
            u = self.parent[self.top[u]];
        }

        if self.depth[v] > self.depth[u] {
            std::mem::swap(&mut v, &mut u);
        }
        (v, u, res)
    }

    pub fn path_query<T, F1, F2>(
        &self,
        sequence_query: F1,
        marge: F2,
        v: usize,
        u: usize,
    ) -> (usize, T)
    where
        T: Clone,
        F1: Fn(std::ops::RangeInclusive<usize>) -> T,
        F2: Fn(&T, &T) -> T,
    {
        let (v, u, mut res) = self.path_query_impl(&sequence_query, &marge, v, u);
        let x = sequence_query(self.vertex_to_index[v]..=self.vertex_to_index[u]);
        res = marge(&res, &x);
        (v, res)
    }

    pub fn path_query_with_edge_value<T, F1, F2>(
        &self,
        sequence_query: F1,
        marge: F2,
        v: usize,
        u: usize,
    ) -> (usize, Option<T>)
    where
        T: Clone,
        F1: Fn(std::ops::RangeInclusive<usize>) -> T,
        F2: Fn(&T, &T) -> T,
    {
        if v == u {
            return (v, None);
        }
        let (v, u, mut res) = self.path_query_impl(&sequence_query, &marge, v, u);
        if v != u {
            let x = sequence_query(self.vertex_to_index[v] + 1..=self.vertex_to_index[u]);
            res = marge(&res, &x);
        }
        (v, Some(res))
    }
}
