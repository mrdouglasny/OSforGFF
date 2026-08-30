# `Dim2.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim2.lean`](../../../OSforGFF/Instances/Dim2.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **two-dimensional** instance of the `GFFPropagator` typeclass. The radial
profile of the free covariance in $d = 2$ is the modified Bessel profile $K_0(mr)/(2\pi)$. The core
work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L49) in closed form: at $d = 2$
the heat-kernel prefactor is $(4\pi t)^{-1}$, so after pulling out the constant $(4\pi)^{-1}$ the
remaining integral is exactly the Schwinger integral
$\int_0^\infty t^{-1}\,e^{-m^2 t - r^2/(4t)}\,dt = 2\,K_0(mr)$, supplied by the master identity
[`schwingerIntegral_eq_besselK0`](../../../OSforGFF/General/BesselK.lean#L237). The file then packages
the closed form as [`instGFFPropagatorDim2`](../../../OSforGFF/Instances/Dim2.lean#L48), together with
the `Fact` order bound $2 \le 2$ for the time/space split.

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 54 lines, 2 definition(s) + 1 theorem(s)/lemma(s)

---

### [`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L29) — Theorem

**Statement**: For mass $m > 0$ and separation $r > 0$, the generic proper-time covariance in two
dimensions collapses to the Bessel-$K_0$ profile:
$$\mathrm{properTimeCovariance}\;2\;m\;r = \frac{1}{2\pi}\,K_0(mr).$$

**Informal**: Rewrites the proper-time integral with the constant-pull-out lemma, recognizes the
$d = 2$ exponent $t^{-2/2} = t^{-1} = 1/t$, applies the Schwinger integral identity, and finishes
with `field_simp`/`ring` (using $\tfrac{1}{4\pi}\cdot 2 = \tfrac{1}{2\pi}$).

**Proof uses**: [`properTimeCovariance_const_mul`](../../../OSforGFF/Covariance/Propagator.lean#L71),
[`schwingerIntegral_eq_besselK0`](../../../OSforGFF/General/BesselK.lean#L237),
`Real.rpow_neg_one`, `Real.pi_ne_zero`

---

### [`instFactTwoLeTwo`](../../../OSforGFF/Instances/Dim2.lean#L44) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeTwo : Fact ((2 : ℕ) ≤ 2)
```

**Informal**: The order bound $2 \le 2$, needed for the time/space split in the generic covariance
construction.

---

### [`instGFFPropagatorDim2`](../../../OSforGFF/Instances/Dim2.lean#L48) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance instGFFPropagatorDim2 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 2 m where
  Cprofile r := if r = 0 then 0 else 1 / (2 * Real.pi) * besselK0 (m * r)
  schwinger_eq r hr := ...
```

**Informal**: The two-dimensional free propagator. Its radial profile `Cprofile` is the Bessel
closed form $K_0(mr)/(2\pi)$, regularized to $0$ at $r = 0$; the required `schwinger_eq` bridge
identifies it with the generic
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L49) for $r > 0$ via
[`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L29).

**Proof uses**: [`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L29),
[`GFFPropagator`](../../../OSforGFF/Covariance/Propagator.lean#L406),
[`besselK0`](../../../OSforGFF/General/BesselK0.lean#L32)

---

*This file has **2** definitions and **1** theorems/lemmas (0 with sorry).*
