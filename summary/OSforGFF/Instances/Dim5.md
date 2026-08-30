# `Dim5.lean` — Informal Summary

> **Source**: [`OSforGFF/Instances/Dim5.lean`](../../../OSforGFF/Instances/Dim5.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

This file supplies the **five-dimensional** instance of the `GFFPropagator` typeclass. The radial
profile of the free covariance in $d = 5$ is the $K_{3/2}$ profile $(1 + mr)\,e^{-mr}/(8\pi^2 r^3)$.
The core work is evaluating the generic proper-time (Schwinger) integral
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L48) in closed form as the order
$\nu = -3/2$ case of the master Bessel identity
[`schwingerIntegral_eq_besselK`](../../../OSforGFF/General/BesselK.lean#L136). The evaluation needs the
half-integer value $K_{3/2}(z) = \sqrt{\pi/(2z)}\,e^{-z}(1 + 1/z)$, proved here as
[`besselK_three_half`](../../../OSforGFF/Instances/Dim5.lean#L52) via the identity
$\cosh(3t/2) = \cosh(t/2)(1 + 4\sinh^2(t/2))$, the substitution $u = \sinh(t/2)$, and the Gaussian
zeroth and second moments (`integral_gaussian_Ioi` and the private
[`gaussian_moment2`](../../../OSforGFF/Instances/Dim5.lean#L32)). Since $d = 5$ is the boundary of the
OS3 proper-time Fubini envelope ($s^{(4-d)/2} = s^{-1/2}$, still integrable) it sits inside the
proven $d \le 5$ range, so the generic master theorem applies. The file supplies the `Fact (5 ≤ 5)`
instance (reusing `Instances.Dim2`'s `Fact (2 ≤ 5)`) and the
[`GFFPropagator 5 m`](../../../OSforGFF/Instances/Dim5.lean#L159) instance.

## Status

**Main result**: Fully proven (0 sorries).

**Length**: 165 lines, 2 definition(s) + 3 theorem(s)/lemma(s)

---

### [`gaussian_moment2`](../../../OSforGFF/Instances/Dim5.lean#L32) — Lemma *(private)*

**Statement**: The Gaussian second moment on the half-line: for $b > 0$,
$$\int_0^\infty u^2\,e^{-b u^2}\,du = \frac{\sqrt{\pi}}{4\,b^{3/2}}.$$

**Informal**: Rewrites $u^2$ as the real power $u^{(2:\mathbb{R})}$, applies mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`, and evaluates $\Gamma(3/2) = \sqrt{\pi}/2$ via
`Real.Gamma_add_one` and `Real.Gamma_one_half_eq`.

**Proof uses**: `integral_rpow_mul_exp_neg_mul_rpow`, `Real.Gamma_add_one`,
`Real.Gamma_one_half_eq`, `Real.rpow_neg`

---

### [`besselK_three_half`](../../../OSforGFF/Instances/Dim5.lean#L52) — Lemma

**Statement**: The half-integer Bessel value of order $3/2$: for $z > 0$,
$$K_{3/2}(z) = \sqrt{\frac{\pi}{2z}}\;e^{-z}\Bigl(1 + \frac{1}{z}\Bigr).$$

**Informal**: Unfolds the `besselK` cosh integral, uses
$\cosh(3t/2) = \cosh(t/2)(1 + 4\sinh^2(t/2))$ and $\cosh t = 1 + 2\sinh^2(t/2)$ to factor out
$e^{-z}$, applies the monotone change of variables $u = \sinh(t/2)$
(`integral_image_eq_integral_deriv_smul_of_monotoneOn`), and splits the resulting integral into the
Gaussian zeroth and second moments, then simplifies with `field_simp`.

**Proof uses**: [`besselK`](../../../OSforGFF/General/BesselK.lean#L37),
`Real.cosh_two_mul`, `Real.cosh_three_mul`, `Real.cosh_sq'`,
`integral_image_eq_integral_deriv_smul_of_monotoneOn`, `integral_gaussian_Ioi`,
[`gaussian_moment2`](../../../OSforGFF/Instances/Dim5.lean#L32)

---

### [`properTimeCovariance_dim5_eq`](../../../OSforGFF/Instances/Dim5.lean#L119) — Theorem

**Statement**: The five-dimensional proper-time covariance is the $K_{3/2}$ profile: for $m, r > 0$,
$$\mathrm{properTimeCovariance}\;5\;m\;r = \frac{(1 + mr)\,e^{-mr}}{8\pi^2 r^3}.$$

**Informal**: Extracts the constant $(4\pi)^{-5/2}$ via the pull-out lemma, specializes the master
identity to order $\nu = -3/2$ (with `besselK_neg` and `besselK_three_half`), and closes with the
power/root simplifications $(r/2m)^{-3/2}\sqrt{\pi/(2mr)} = 2m\sqrt{\pi}/r^2$ and
$(4\pi)^{-5/2} = 1/(32\pi^2\sqrt{\pi})$, then `field_simp`/`ring`.

**Proof uses**: [`properTimeCovariance_const_mul`](../../../OSforGFF/Covariance/Propagator.lean#L70),
[`schwingerIntegral_eq_besselK`](../../../OSforGFF/General/BesselK.lean#L136),
[`besselK_neg`](../../../OSforGFF/General/BesselK.lean#L52),
[`besselK_three_half`](../../../OSforGFF/Instances/Dim5.lean#L52),
`Real.rpow_neg`, `Real.rpow_add`, `Real.sqrt_mul`, `Real.sqrt_sq`

---

### [`instFactFiveLeFive`](../../../OSforGFF/Instances/Dim5.lean#L155) — Definition *(instance)*

**Lean signature**
```lean
instance instFactFiveLeFive : Fact ((5 : ℕ) ≤ 5)
```

**Informal**: The boundary order bound $5 \le 5$, entering the OS3 proper-time Fubini domination.
(`Fact ((2:ℕ) ≤ 5)` is provided separately by `Instances.Dim2`'s `instFactTwoLeFive`.)

---

### [`instGFFPropagatorDim5`](../../../OSforGFF/Instances/Dim5.lean#L159) — Definition *(instance)*

**Lean signature**
```lean
noncomputable instance instGFFPropagatorDim5 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 5 m where
  Cprofile r := if r = 0 then 0 else (1 + m * r) * Real.exp (-(m * r)) / (8 * Real.pi ^ 2 * r ^ 3)
  schwinger_eq r hr := ...
```

**Informal**: The five-dimensional free propagator. Its radial profile `Cprofile` is the $K_{3/2}$
closed form $(1 + mr)\,e^{-mr}/(8\pi^2 r^3)$, regularized to $0$ at $r = 0$; the required
`schwinger_eq` bridge identifies it with the generic
[`properTimeCovariance`](../../../OSforGFF/Covariance/Propagator.lean#L48) for $r > 0$ via
[`properTimeCovariance_dim5_eq`](../../../OSforGFF/Instances/Dim5.lean#L119).

**Proof uses**: [`properTimeCovariance_dim5_eq`](../../../OSforGFF/Instances/Dim5.lean#L119),
[`GFFPropagator`](../../../OSforGFF/Covariance/Propagator.lean#L405)

---

*This file has **2** definitions and **3** theorems/lemmas (0 with sorry).*
