# `Dim4.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim4.lean`](../../../OSforGFF/Instances/Dim4.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **four-dimensional** instance of the `GFFPropagator` typeclass. The radial
profile of the free covariance in $d = 4$ is the Bessel closed form $(m/(4\pi^2 r))\,K_1(mr)$. The
core work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean) in closed form as the order
$\nu = -1$ case of the master identity
[`schwingerIntegral_eq_besselK1`](../../../OSforGFF/General/BesselK.lean). The file packages the
closed form as [`instGFFPropagatorDim4`](../../../OSforGFF/Instances/Dim4.lean#L50) and supplies the
`Fact` order bound $2 \le 4$ (time/space split).

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 56 lines, 2 definition(s) + 1 theorem(s)/lemma(s)

---

### [`properTimeCovariance_dim4_eq`](../../../OSforGFF/Instances/Dim4.lean#L26) — Theorem

**Statement**: For mass $m > 0$ and separation $r > 0$, the generic proper-time covariance in four
dimensions collapses to the Bessel-$K_1$ profile:
$$\mathrm{properTimeCovariance}\;4\;m\;r = \frac{m}{4\pi^2 r}\,K_1(mr).$$

**Informal**: Rewrites the proper-time integral with the constant-pull-out lemma, recognizes the
$d = 4$ exponent $t^{-4/2} = t^{-2} = 1/t^2$, applies the master Schwinger–$K_1$ identity, and
finishes with `field_simp`.

**Proof uses**: [`properTimeCovariance_const_mul`](../../../OSforGFF/Covariance/Propagator.lean),
[`schwingerIntegral_eq_besselK1`](../../../OSforGFF/General/BesselK.lean),
`Real.rpow_neg`, `Real.rpow_two`, `Real.pi_ne_zero`

---

### [`instFactTwoLeFour`](../../../OSforGFF/Instances/Dim4.lean#L46) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeFour : Fact ((2 : ℕ) ≤ 4)
```

**Informal**: The order bound $2 \le 4$, needed for the time/space split in the generic covariance
construction.

---

### [`instGFFPropagatorDim4`](../../../OSforGFF/Instances/Dim4.lean#L50) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance instGFFPropagatorDim4 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 4 m where
  Cprofile r := if r = 0 then 0 else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)
  schwinger_eq r hr := ...
```

**Informal**: The four-dimensional free propagator. Its radial profile `Cprofile` is the Bessel
closed form $(m/(4\pi^2 r))\,K_1(mr)$, regularized to $0$ at $r = 0$; the required `schwinger_eq`
bridge identifies it with the generic
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean) for $r > 0$ via
[`properTimeCovariance_dim4_eq`](../../../OSforGFF/Instances/Dim4.lean#L26).

**Proof uses**: [`properTimeCovariance_dim4_eq`](../../../OSforGFF/Instances/Dim4.lean#L26),
[`GFFPropagator`](../../../OSforGFF/Covariance/Propagator.lean),
[`besselK1`](../../../OSforGFF/General/BesselFunction.lean#L27)

---

*This file has **2** definitions and **1** theorem (0 with sorry).*
