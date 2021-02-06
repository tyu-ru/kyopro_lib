use criterion::{criterion_group, criterion_main, Criterion};
use itertools::{izip, Itertools};

use klalgebra::predefined as algebra;
use klsegtree::*;

fn gen_rnd_dat<T>(n: usize, range: std::ops::Range<T>) -> Vec<T>
where
    T: rand::distributions::uniform::SampleUniform,
{
    use rand::distributions::{Distribution, Uniform};
    let d = Uniform::from(range);
    let mut rng = rand::thread_rng();
    (0..n).map(|_| d.sample(&mut rng)).collect()
}
fn gen_rnd_dat2(n: usize, range: std::ops::Range<usize>) -> Vec<(usize, usize)> {
    izip!(gen_rnd_dat(n, range.clone()), gen_rnd_dat(n, range))
        .map(|(s, e)| if s <= e { (s, e) } else { (e, s) })
        .collect()
}

fn bench_segtree(c: &mut Criterion) {
    let n = 10_000;

    let q = izip!(
        gen_rnd_dat(n, 0..n),
        gen_rnd_dat(n, -10000i64..10000i64),
        gen_rnd_dat2(n, 0..n)
    )
    .collect_vec();

    let mut st = SegTree::build_from_slice(&gen_rnd_dat(n, -10000..10000), algebra::Add::new());
    c.bench_function("segtree", |b| {
        b.iter(|| {
            for &(i, c, (a, b)) in &q {
                st.update(i, c);
                st.query(a..b);
            }
        })
    });
}

fn bench_segtree_binsearch(c: &mut Criterion) {
    let n = 10_000;
    let q = izip!(
        gen_rnd_dat(n, 0..n),
        gen_rnd_dat(n, 0..10000),
        gen_rnd_dat(n, 0..n),
        gen_rnd_dat(n, 0..10000)
    )
    .collect_vec();
    let mut st = SegTree::build_from_slice(&gen_rnd_dat(n, 0..10000), algebra::Add::new());
    c.bench_function("segtree-binsearch", |b| {
        b.iter(|| {
            for &(i, x, j, y) in &q {
                st.update(i, x);
                st.max_right(j, |&s| s <= y);
                st.min_left(j, |&s| s <= y);
            }
        })
    });
}

fn bench_lazy_segtree(c: &mut Criterion) {
    let n = 10_000;

    // let mut lst = LazySegTree::build_from_slice(
    //     &gen_rnd_dat(n, -10000i64..10000),
    //     monoid_with_act(
    //         algebra::Add::new(),
    //         algebra::Add::new(),
    //         |a: &i64, b: &i64, l| a + b * l as i64,
    //     ),
    // );

    let mut lst =
        LazySegTree::build_from_slice(&gen_rnd_dat(n, -10000i64..10000), predefined::RAQRSQ::new());
    let q = izip!(
        gen_rnd_dat(n, -10000i64..10000i64),
        gen_rnd_dat2(n, 0..n),
        gen_rnd_dat2(n, 0..n)
    )
    .collect_vec();

    c.bench_function("lazy-segtree", |b| {
        b.iter(|| {
            for &(x, (a, b), (c, d)) in &q {
                lst.update_range(a..b, x);
                lst.query(c..d);
            }
        })
    });
}

criterion_group!(
    benches,
    bench_segtree,
    bench_segtree_binsearch,
    bench_lazy_segtree
);
criterion_main!(benches);
