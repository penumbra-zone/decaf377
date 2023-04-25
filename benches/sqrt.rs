use ark_ed_on_bls12_377::Fq;
use ark_ff::{Field, PrimeField, Zero};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use decaf377::{SqrtRatioZeta, ZETA};
use rand_chacha::ChaChaRng;
use rand_core::{RngCore, SeedableRng};

fn sqrt_original(u: &Fq, v: &Fq) -> (bool, Fq) {
    if u.is_zero() {
        return (true, *u);
    }
    if v.is_zero() {
        return (false, *v);
    }

    let uv = v.inverse().expect("nonzero") * u;
    if let Some(sqrt_uv) = uv.sqrt() {
        (true, sqrt_uv)
    } else {
        let sqrt_zeta_uv = (*ZETA * uv)
            .sqrt()
            .expect("must be square if u/v nonsquare");
        (false, sqrt_zeta_uv)
    }
}

pub fn bench_sqrt_ratio(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt");
    let n = 10;
    let mut rng = ChaChaRng::seed_from_u64(666);
    let mut test_field_elements = Vec::with_capacity(n);
    for _ in 0..n {
        let mut i_bytes = [0u8; 32];
        let mut j_bytes = [0u8; 32];
        rng.fill_bytes(&mut i_bytes);
        rng.fill_bytes(&mut j_bytes);
        test_field_elements.push((
            Fq::from_le_bytes_mod_order(&i_bytes[..]),
            Fq::from_le_bytes_mod_order(&j_bytes[..]),
        ))
    }

    for (i, j) in test_field_elements {
        group.bench_with_input(
            BenchmarkId::new("Arkworks", format!("{}/{}", i, j)),
            &(&i, &j),
            |b, (i, j)| b.iter(|| sqrt_original(i, j)),
        );
        group.bench_with_input(
            BenchmarkId::new("Sarkar2020", format!("{}/{}", i, j)),
            &(&i, &j),
            |b, (i, j)| b.iter(|| Fq::sqrt_ratio_zeta(i, j)),
        );
    }
    group.finish();
}

criterion_group!(benches, bench_sqrt_ratio);
criterion_main!(benches);
