use criterion::{criterion_group, criterion_main, Criterion};
use kyopro_lib::segtree::SegTree;

fn bench_segtree(c: &mut Criterion) {
    use rand::distributions::{Distribution, Uniform};
    let n = 10_000;
    let d = Uniform::from(0..n);
    let d2 = Uniform::from(-(n as i64)..=n as i64);
    let mut rng = rand::thread_rng();
    let q = (0..n)
        .map(|_| {
            let i = d.sample(&mut rng);
            let c = d2.sample(&mut rng);
            let mut a = d.sample(&mut rng);
            let mut b = d.sample(&mut rng);
            if a > b {
                std::mem::swap(&mut a, &mut b);
            }
            (i, c, a, b)
        })
        .collect::<Vec<_>>();

    let mut st = SegTree::new(n, 0, |&a, &b| a + b);
    c.bench_function("segtree", |b| {
        b.iter(|| {
            for &(i, c, a, b) in &q {
                st.update(i, c);
                st.query(a..b);
            }
        })
    });
}

criterion_group!(benches, bench_segtree);
criterion_main!(benches);
