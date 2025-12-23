use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

use plid::Plid;

fn plid_parse(c: &mut Criterion) {
    c.bench_function("Plid FromStr", |b| {
        b.iter(|| black_box("usr_06DJX8T67BP71A4MYW9VXNR".parse::<Plid>()))
    });
}

fn plid_gen(c: &mut Criterion) {
    c.bench_function("Plid gen", |b| {
        b.iter(|| black_box(Plid::gen("abc", || 0, |_| true, Ok)))
    });
}

criterion_group!(benches, plid_parse, plid_gen);
criterion_main!(benches);
