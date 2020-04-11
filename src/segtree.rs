pub struct SegTree<T, F> {
    n: usize,
    id: T,
    x: Vec<T>,
    f: F,
}

impl<T, F> SegTree<T, F>
where
    T: std::marker::Copy,
    F: Fn(&T, &T) -> T,
{
    pub fn new(n: usize, id: T, f: F) -> Self {
        let n = 1 << crate::misc::log2p1(n - 1);
        Self {
            n: n,
            id: id,
            x: vec![id; n * 2],
            f: f,
        }
    }
    pub fn update(&mut self, i: usize, x: T) {
        let mut i = self.n + i - 1;
        self.x[i] = x;
        while i > 0 {
            i = (i - 1) / 2;
            self.x[i] = (self.f)(&self.x[i * 2 + 1], &self.x[i * 2 + 2]);
        }
    }
    pub fn query(&self, r: std::ops::Range<usize>) -> T {
        self.query_impl(0, r, 0..self.n)
    }
    fn query_impl(&self, k: usize, r: std::ops::Range<usize>, a: std::ops::Range<usize>) -> T {
        if r.end <= a.start || a.end <= r.start {
            self.id
        } else if r.start <= a.start && a.end <= r.end {
            self.x[k]
        } else {
            (self.f)(
                &self.query_impl(k * 2 + 1, r.clone(), a.start..(a.start + a.end) / 2),
                &self.query_impl(k * 2 + 2, r, (a.start + a.end) / 2..a.end),
            )
        }
    }
}

#[test]
fn test_segtree() {
    let mut st = SegTree::new(4, 0, |&a, &b| a + b);
    st.update(0, 1);
    st.update(1, 2);
    st.update(2, 3);
    st.update(3, 4);
    assert_eq!(st.query(0..4), 10);
    assert_eq!(st.query(0..1), 1);
    assert_eq!(st.query(0..2), 3);
    assert_eq!(st.query(1..3), 5);
}
