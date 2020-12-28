pub struct Tree {
    pub edge: Vec<Vec<usize>>,
}

impl Tree {
    pub fn new(n: usize) -> Self {
        Tree {
            edge: vec![vec![]; n],
        }
    }
    pub fn new_with_edge(e: &[(usize, usize)]) -> Self {
        let mut res = Self::new(e.len() + 1);
        for (i, j) in e {
            res.add_edge(*i, *j);
        }
        res
    }
    pub fn add_edge(&mut self, i: usize, j: usize) {
        self.edge[i].push(j);
        self.edge[j].push(i);
    }

    pub fn bfs<F: FnMut(usize)>(&self, root: usize, mut f: F) {
        let mut q = std::collections::VecDeque::new();
        q.push_back((root, root));
        while let Some((node, from)) = q.pop_front() {
            f(node);
            for &e in self.edge[node].iter().filter(|&x| *x != from) {
                q.push_back((e, node));
            }
        }
    }
    pub fn dfs<B, I, C, M, F>(&self, root: usize, mut init: I, mut c: C, marge: M, mut fin: F) -> B
    where
        I: FnMut(usize) -> B,
        C: FnMut(usize, usize),
        M: Fn(&mut B, B),
        F: FnMut(usize, B) -> B,
    {
        self.dfs_impl(root, root, &mut init, &mut c, &marge, &mut fin)
    }
    fn dfs_impl<B, I, C, M, F>(
        &self,
        root: usize,
        from: usize,
        init: &mut I,
        c: &mut C,
        marge: &M,
        fin: &mut F,
    ) -> B
    where
        I: FnMut(usize) -> B,
        C: FnMut(usize, usize),
        M: Fn(&mut B, B),
        F: FnMut(usize, B) -> B,
    {
        let mut x = init(root);
        for &n in self.edge[root].iter().filter(|&x| *x != from) {
            c(root, n);
            marge(&mut x, self.dfs_impl(n, root, init, c, marge, fin));
        }
        fin(root, x)
    }
}

#[cfg(test)]
#[test]
fn test_tree_bfs() {
    let tree = Tree::new_with_edge(&[(0, 1), (1, 2), (1, 3), (4, 2), (3, 5)]);

    let mut v = vec![];
    tree.bfs(0, |i| v.push(i));
    assert_eq!(v, &[0, 1, 2, 3, 4, 5]);

    let mut v = vec![];
    tree.bfs(2, |i| v.push(i));
    assert_eq!(v, &[2, 1, 4, 0, 3, 5]);
}

#[cfg(test)]
#[test]
fn test_tree_dfs() {
    let tree = Tree::new_with_edge(&[(0, 1), (1, 2), (1, 3), (4, 2), (3, 5)]);

    let mut v = vec![];
    tree.dfs(0, |i| v.push(i), |_, _| {}, |_, _| {}, |_, _| {});
    assert_eq!(v, &[0, 1, 2, 4, 3, 5]);

    let mut v = vec![];
    tree.dfs(2, |i| v.push(i), |_, _| {}, |_, _| {}, |_, _| {});
    assert_eq!(v, &[2, 1, 0, 3, 5, 4]);
}
