
#[derive(Clone)]
struct Edge {
    to: usize,
    rev_index: usize,
    capacity: u64,
}

pub struct MaxFlowGraph {
    n: usize,
    g: Vec<Vec<Edge>>,
}

impl MaxFlowGraph {
    pub fn new(n: usize) -> Self {
        Self { n, g: vec![vec![]; n] }
    }

    pub fn add_edge(&mut self, v: usize, u: usize, capacity: u64) {
        let idx = self.g[v].len();
        let rev_index = self.g[u].len();
        self.g[v].push(Edge{ to: u, rev_index, capacity });
        self.g[u].push(Edge{ to: v, rev_index: idx, capacity: 0 });
    }

    pub fn ford_fulkerson(&mut self, s: usize, t: usize) -> u64 {
        let mut res = 0;
        loop {
            let f = self.dfs(&mut vec![false; self.n], s, t, std::u64::MAX);
            if f == 0 {
                break;
            }
            res += f;
        }
        res
    }

    fn dfs(&mut self, flag: &mut Vec<bool>, v: usize, t: usize, mn: u64) -> u64 {
        flag[v] = true;
        if v == t {
            return mn;
        }
        for i in 0..self.g[v].len() {
            let Edge{ to, rev_index, capacity } = self.g[v][i];
            if flag[to] || capacity == 0 {
                continue;
            }
            let f = self.dfs(flag, to, t, std::cmp::min(mn, capacity));
            if 0 < f {
                self.g[v][i].capacity -= f;
                self.g[to][rev_index].capacity += f;
                return f;
            }
        }
        0
    }
}
