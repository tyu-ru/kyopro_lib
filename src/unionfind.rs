// use num_derive::{Num, NumOps, One, Zero};

#[derive(Clone, Copy, PartialEq, PartialOrd)]
struct Size(usize);
#[derive(Clone, Copy)]
struct Parent(usize);

#[derive(Clone)]
enum Node {
    Root(Size),
    Leaf(Parent),
}

struct RootInfo {
    idx: usize,
    size: Size,
}

pub struct UnionFind {
    node: Vec<Node>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            node: vec![Node::Root(Size(1)); n],
        }
    }

    pub fn root(&mut self, i: usize) -> usize {
        self.root_impl(i).idx
    }
    fn root_impl(&mut self, i: usize) -> RootInfo {
        match self.node[i] {
            Node::Root(s) => RootInfo { idx: i, size: s },
            Node::Leaf(Parent(p)) => {
                let r = self.root_impl(p);
                self.node[i] = Node::Leaf(Parent(r.idx));
                r
            }
        }
    }
    pub fn unite(&mut self, u: usize, v: usize) -> bool {
        let mut u = self.root_impl(u);
        let mut v = self.root_impl(v);
        if u.idx == v.idx {
            return false;
        }
        if u.size < v.size {
            std::mem::swap(&mut u, &mut v);
        }
        self.node[u.idx] = Node::Root(Size(u.size.0 + v.size.0));
        self.node[v.idx] = Node::Leaf(Parent(u.idx));
        true
    }
    pub fn size(&mut self, i: usize) -> usize {
        self.root_impl(i).size.0
    }
    pub fn is_same(&mut self, i: usize, j: usize) -> bool {
        self.root(i) == self.root(j)
    }
}

#[cfg(test)]
#[test]
fn test_unionfind() {
    let mut uf = UnionFind::new(5);
    assert_eq!(uf.size(0), 1);
    assert_eq!(uf.unite(0, 1), true);
    assert_eq!(uf.is_same(0, 1), true);
    assert_eq!(uf.size(0), 2);
    assert_eq!(uf.size(1), 2);
    assert_eq!(uf.unite(1, 2), true);
    assert_eq!(uf.is_same(0, 2), true);
    assert_eq!(uf.size(2), 3);
    assert_eq!(uf.unite(0, 0), false);
    assert_eq!(uf.size(0), 3);
}

pub struct UnionFindWithCS<T, F> {
    uf: UnionFind,
    val: Vec<Option<T>>,
    f: F,
}

impl<T, F> UnionFindWithCS<T, F>
where
    F: Fn(T, T) -> T,
{
    pub fn new<F2: Fn(usize) -> T>(n: usize, g: F2, f: F) -> Self {
        Self {
            uf: UnionFind::new(n),
            val: (0..n).map(|i| Some(g(i))).collect(),
            f: f,
        }
    }

    pub fn root(&mut self, i: usize) -> usize {
        self.uf.root(i)
    }
    pub fn unite(&mut self, u: usize, v: usize) -> bool {
        let mut u = self.uf.root_impl(u);
        let mut v = self.uf.root_impl(v);
        if u.idx == v.idx {
            return false;
        }
        if u.size < v.size {
            std::mem::swap(&mut u, &mut v);
        }
        self.uf.node[v.idx] = Node::Leaf(Parent(u.idx));
        self.uf.node[u.idx] = Node::Root(Size(u.size.0 + v.size.0));
        self.val[u.idx] = Some((self.f)(
            self.val[u.idx].take().unwrap(),
            self.val[v.idx].take().unwrap(),
        ));
        true
    }
    pub fn size(&mut self, i: usize) -> usize {
        self.uf.root_impl(i).size.0
    }
    pub fn is_same(&mut self, i: usize, j: usize) -> bool {
        self.root(i) == self.root(j)
    }

    pub fn value(&mut self, i: usize) -> &mut T {
        self.val[self.uf.root(i)].as_mut().unwrap()
    }
}
