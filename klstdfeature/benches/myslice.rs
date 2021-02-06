use criterion::{criterion_group, criterion_main, Criterion};
use itertools::Itertools;
use rand::prelude::*;

use klstdfeature::prelude::*;

fn bench_myslice_select_nth_unstable(c: &mut Criterion) {
    let n = 10_000; // data len
    let m = 100; // test data len
    let v = (0..m)
        .map(|_| {
            let mut v = (0..n).collect_vec();
            v.shuffle(&mut thread_rng());
            (v, thread_rng().gen_range(0, n))
        })
        .collect_vec();

    c.bench_function("bench_myslice_select_nth_unstable", |b| {
        b.iter_batched(
            || v.clone(),
            |dat| {
                for (mut v, idx) in dat {
                    select_nth_unstable1(&mut v, idx);
                }
            },
            criterion::BatchSize::LargeInput,
        );
    });
}

criterion_group!(benches, bench_myslice_select_nth_unstable);
criterion_main!(benches);
