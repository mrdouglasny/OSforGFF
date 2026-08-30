# `Dim2.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim2.lean`](../../../OSforGFF/Instances/Dim2.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **two-dimensional** instance of the `GFFPropagator` typeclass. The radial
profile of the free covariance in $d = 2$ is the modified Bessel profile $K_0(mr)/(2\pi)$. The core
work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L48) in closed form: at $d = 2$
the heat-kernel prefactor is $(4\pi t)^{-1}$, so after pulling out the constant $(4\pi)^{-1}$ the
remaining integral is exactly the Schwinger integral
$\int_0^\infty t^{-1}\,e^{-m^2 t - r^2/(4t)}\,dt = 2\,K_0(mr)$, supplied by the master identity
[`schwingerIntegral_eq_besselK0`](../../../OSforGFF/General/BesselK.lean#L236). The file then packages
the closed form as [`instGFFPropagatorDim2`](../../../OSforGFF/Instances/Dim2.lean#L50), together with
two `Fact` order bounds — $2 \le 2$ for the time/space split, and $2 \le 5$ for the OS3 proper-time
Fubini domination (the latter is reused by `Instances.Dim5`).

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 57 lines, 3 definition(s) + 1 theorem(s)/lemma(s)

---

### [`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L28) — Theorem

**Statement**: For mass $m > 0$ and separation $r > 0$, the generic proper-time covariance in two
dimensions collapses to the Bessel-$K_0$ profile:
$$\mathrm{properTimeCovariance}\;2\;m\;r = \frac{1}{2\pi}\,K_0(mr).$$

**Informal**: Rewrites the proper-time integral with the constant-pull-out lemma, recognizes the
$d = 2$ exponent $t^{-2/2} = t^{-1} = 1/t$, applies the Schwinger integral identity, and finishes
with `field_simp`/`ring` (using $\tfrac{1}{4\pi}\cdot 2 = \tfrac{1}{2\pi}$).

**Proof uses**: [`properTimeCovariance_const_mul`](../../../OSforGFF/Covariance/Propagator.lean#L70),
[`schwingerIntegral_eq_besselK0`](../../../OSforGFF/General/BesselK.lean#L236),
`Real.rpow_neg_one`, `Real.pi_ne_zero`

---

### [`instFactTwoLeTwo`](../../../OSforGFF/Instances/Dim2.lean#L43) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeTwo : Fact ((2 : ℕ) ≤ 2)
```

**Informal**: The order bound $2 \le 2$, needed for the time/space split in the generic covariance
construction.

---

### [`instFactTwoLeFive`](../../../OSforGFF/Instances/Dim2.lean#L46) — Definition *(instance)*

**Lean signature**
```lean
instance instFactTwoLeFive : Fact ((2 : ℕ) ≤ 5)
```

**Informal**: The order bound $2 \le 5$, entering the OS3 proper-time Fubini domination. This
instance is reused by `Instances.Dim5`.

---

### [`instGFFPropagatorDim2`](../../../OSforGFF/Instances/Dim2.lean#L50) — Definition *(instance)*

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
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L48) for $r > 0$ via
[`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L28).

**Proof uses**: [`properTimeCovariance_dim2_eq`](../../../OSforGFF/Instances/Dim2.lean#L28),
[`GFFPropagator`](../../../OSforGFF/Covariance/Propagator.lean#L405),
[`besselK0`](../../../OSforGFF/General/BesselK0.lean#L31)

---

*This file has **3** definitions and **1** theorems/lemmas (0 with sorry).*
