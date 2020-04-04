struct Node {
    parent: usize,
    size: usize,
}

pub struct UnionFind {
    node: Vec<Node>,
}
impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            node: (0..n).map(|i| Node { parent: i, size: 1 }).collect(),
        }
    }

    fn root(&mut self, i: usize) -> usize {
        if self.node[i].parent == i {
            return i;
        }
        let r = self.root(self.node[i].parent);
        self.node[i].parent = r;
        r
    }
    pub fn unite(&mut self, i: usize, j: usize) {
        let i = self.root(i);
        let j = self.root(j);
        self.node[i].parent = j;
        self.node[j].size += std::mem::replace(&mut self.node[i].size, 0);
    }
    pub fn size(&mut self, i: usize) -> usize {
        let r = self.root(i);
        self.node[r].size
    }
    pub fn is_same(&mut self, i: usize, j: usize) -> bool {
        self.root(i) == self.root(j)
    }
}

#[test]
fn test_unionfind() {
    let mut uf = UnionFind::new(5);
    assert_eq!(uf.size(0), 1);
    uf.unite(0, 1);
    assert_eq!(uf.is_same(0, 1), true);
    assert_eq!(uf.size(0), 2);
    assert_eq!(uf.size(1), 2);
    uf.unite(1, 2);
    assert_eq!(uf.is_same(0, 2), true);
    assert_eq!(uf.size(2), 3);
    uf.unite(0, 0);
    assert_eq!(uf.size(0), 3);
}
