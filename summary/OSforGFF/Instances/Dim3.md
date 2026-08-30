# `Dim3.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim3.lean`](../../../OSforGFF/Instances/Dim3.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **three-dimensional (Yukawa)** instance of the `GFFPropagator` typeclass.
The radial profile of the free covariance in $d = 3$ is the Yukawa potential $e^{-mr}/(4\pi r)$.
The core work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L49) in closed form as the order
$\nu = -1/2$ case of the master Bessel identity
[`schwingerIntegral_eq_besselK`](../../../OSforGFF/General/BesselK.lean#L137), evaluated with the
elementary half-integer value [`besselK_half`](../../../OSforGFF/General/BesselK.lean#L193)
($K_{1/2}(z) = \sqrt{\pi/(2z)}\,e^{-z}$). The file then packages the closed form as
[`instGFFPropagatorDim3`](../../../OSforGFF/Instances/Dim3.lean#L78), together with the `Fact` order
bound $2 \le 3$ (time/space split).

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 84 lines, 2 definition(s) + 2 theorem(s)/lemma(s)

---

### [`schwingerIntegral_dim3`](../../../OSforGFF/Instances/Dim3.lean#L29) — Theorem

**Statement**: The three-dimensional proper-time integral in closed form: for $m, r > 0$,
$$\int_0^\infty t^{-3/2}\,e^{-m^2 t - r^2/(4t)}\,dt = \frac{2\sqrt{\pi}}{r}\,e^{-mr}.$$

**Informal**: Specializes the master identity to order $\nu = -1/2$, uses `besselK_neg` and
`besselK_half` to evaluate $K_{-1/2} = K_{1/2}$, and simplifies the resulting power/root factors
$(r/2m)^{-1/2}\sqrt{\pi/(2mr)} = \sqrt{\pi}/r$ with `Real.sqrt_mul`/`Real.sqrt_sq` and `ring`.

**Proof uses**: [`schwingerIntegral_eq_besselK`](../../../OSforGFF/General/BesselK.lean#L137),
[`besselK_neg`](../../../OSforGFF/General/BesselK.lean#L53),
[`besselK_half`](../../../OSforGFF/General/BesselK.lean#L193),
`Real.rpow_neg`, `Real.sqrt_eq_rpow`, `Real.sqrt_mul`, `Real.sqrt_sq`

---

### [`properTimeCovariance_dim3_eq`](../../../OSforGFF/Instances/Dim3.lean#L51) — Theorem

**Statement**: The three-dimensional proper-time covariance is the Yukawa profile: for $m, r > 0$,
$$\mathrm{properTimeCovariance}\;3\;m\;r = \frac{e^{-mr}}{4\pi r}.$$

**Informal**: Extracts the constant $(4\pi)^{-3/2}$ via the pull-out lemma, applies
`schwingerIntegral_dim3`, and closes using the constant identity
$(4\pi)^{-3/2}\cdot 2\sqrt{\pi} = 1/(4\pi)$ (proved by splitting $(4\pi)^{3/2}$ and `field_simp`).

**Proof uses**: [`properTimeCovariance_const_mul`](../../../OSforGFF/Covariance/Propagator.lean#L71),
[`schwingerIntegral_dim3`](../../../OSforGFF/Instances/Dim3.lean#L29),
`Real.rpow_neg`, `Real.rpow_add`, `Real.sqrt_mul`, `Real.sqrt_sq`

---

### [`instFactTwoLeThree`](../../../OSforGFF/Instances/Dim3.lean#L74) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeThree : Fact ((2 : ℕ) ≤ 3)
```

**Informal**: The order bound $2 \le 3$, needed for the time/space split in the generic covariance
construction.

---

### [`instGFFPropagatorDim3`](../../../OSforGFF/Instances/Dim3.lean#L78) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance instGFFPropagatorDim3 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 3 m where
  Cprofile r := if r = 0 then 0 else Real.exp (-(m * r)) / (4 * Real.pi * r)
  schwinger_eq r hr := ...
```

**Informal**: The three-dimensional free propagator. Its radial profile `Cprofile` is the Yukawa
closed form $e^{-mr}/(4\pi r)$, regularized to $0$ at $r = 0$; the required `schwinger_eq` bridge
identifies it with the generic
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L49) for $r > 0$ via
[`properTimeCovariance_dim3_eq`](../../../OSforGFF/Instances/Dim3.lean#L51).

**Proof uses**: [`properTimeCovariance_dim3_eq`](../../../OSforGFF/Instances/Dim3.lean#L51),
[`GFFPropagator`](../../../OSforGFF/Covariance/Propagator.lean#L406)

---

*This file has **2** definitions and **2** theorems/lemmas (0 with sorry).*
