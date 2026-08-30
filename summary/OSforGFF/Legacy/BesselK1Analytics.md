# `BesselK1Analytics.lean` — Informal Summary

> **Source**: [`OSforGFF/Legacy/BesselK1Analytics.lean`](../../../OSforGFF/Legacy/BesselK1Analytics.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

**This is LEGACY, off-graph code.** The file collects the analytic properties of the modified
Bessel function `besselK1` (from `General/BesselFunction.lean`), understood through its integral
representation
$$K_1(z) = \int_0^\infty e^{-z\cosh t}\,\cosh t\; dt.$$
These positivity, continuity, asymptotic, near-origin, and integrability lemmas supported the
original four-dimensional Bessel-covariance analysis. As the file's own header records, they are
consumed **only** by `OSforGFF/Legacy/Dim4Bessel.lean` (the quarantined 4D program) and are **not
on the root import graph** — `lake build` does not compile this file. It is verified in isolation
with

    lake env lean OSforGFF/Legacy/BesselK1Analytics.lean

The dimension-generic library needs none of these lemmas: the covariance's $L^1$-integrability,
Fourier transform, and exponential decay are established generically from the proper-time
representation (`Covariance/Propagator.lean`, `Covariance/ParsevalGeneric.lean`), and the closed-form
`K₁` Schwinger identity is the order $\nu = -1$ case of the master identity
`schwingerIntegral_eq_besselK` in `General/BesselK`. The content is preserved because it is genuine
proven mathematics.

## Status

**Main result**: Fully proven (0 sorries — `grep` for `sorry`/`admit` returns none). The lemmas
culminate in `radial_besselK1_integrable`, the $L^1$-integrability of the radial profile
$r \mapsto r^2 K_1(mr)$ that underpins the 4D free-covariance kernel's integrability.

**Length**: 844 lines, 0 definitions + 6 theorems/lemmas.

---

### [`besselK1_pos`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L35) — Lemma

**Statement**: For $z > 0$, the Bessel function is strictly positive:
$$0 < K_1(z).$$

**Informal**: The integrand $f(t) = e^{-z\cosh t}\cosh t$ is everywhere strictly positive and
integrable on $[0,\infty)$ (via super-exponential decay), so its integral is positive.

**Proof uses**: strict positivity and continuity of $f$; integrability from
`integrable_of_isBigO_exp_neg` with the bound $f(t)/e^{-t} \to 0$ (using
$\tfrac{1}{2}e^t \le \cosh t \le e^t$ and $t/e^t \to 0$);
`MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`.

---

### [`besselK1_continuousOn`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L195) — Lemma

**Statement**: $K_1$ is continuous on the open half-line:
$$\mathrm{ContinuousOn}\; K_1\; (0, \infty).$$

**Informal**: Continuity at each $z_0 > 0$ follows from dominated convergence, using the
$z$-independent dominating function $e^{-(z_0/2)\cosh t}\cosh t$ valid for $z \ge z_0/2$.

**Proof uses**: `MeasureTheory.continuousAt_of_dominated`; integrability of the dominating bound
(split $[0,\infty) = [0,1] \cup [1,\infty)$, compactness on $[0,1]$ and super-exponential decay on
$[1,\infty)$).

---

### [`besselK1_asymptotic`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L294) — Lemma

**Statement**: For $z \ge 1$, $K_1$ decays exponentially:
$$K_1(z) \le (\sinh 1 + 2)\, e^{-z}.$$

**Informal**: Splitting the defining integral at $t = 1$: on $[0,1]$ the integrand is bounded by
$e^{-z}\cosh t$ (integral $\le \sinh 1 \cdot e^{-z}$), and on $[1,\infty)$ a proper-time bound with
antiderivative $F(t) = -\tfrac{2}{z}e^{-z e^t/2}$ gives $\le 2 e^{-z}$.

**Proof uses**: FTC (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`,
`integral_Ioi_of_hasDerivAt_of_tendsto`); $\tfrac12 e^t \le \cosh t \le e^t$; `add_one_le_exp`.

---

### [`besselK1_mul_self_le`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L473) — Lemma

**Statement**: For $0 < z \le 1$, the product $z\,K_1(z)$ is uniformly bounded:
$$z \cdot K_1(z) \le \cosh 1 + 2.$$

**Informal**: Splitting at $t = 1$: on $[0,1]$ the integrand is $\le \cosh 1$ (giving
$z \int_0^1 f \le z\cosh 1 \le \cosh 1$), and on $[1,\infty)$ the proper-time antiderivative bound
gives $z\int_1^\infty f \le 2$.

**Proof uses**: `setIntegral_mono_on`; the antiderivative $F(t) = -\tfrac{2}{z}e^{-z e^t/2}$ and
`integral_Ioi_of_hasDerivAt_of_tendsto`; `exp_le_one_iff`.

---

### [`besselK1_near_origin_bound`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L689) — Lemma

**Statement**: For $0 < z \le 1$, the near-origin singularity is at most $1/z$:
$$K_1(z) \le \frac{\cosh 1 + 2}{z}.$$

**Informal**: Immediate rearrangement of `besselK1_mul_self_le`.

**Proof uses**: [`besselK1_mul_self_le`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L473),
`le_div_iff₀'`.

---

### [`radial_besselK1_integrable`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L702) — Lemma

**Statement**: For $m > 0$, the radial integrand is integrable on $(0,\infty)$:
$$r \mapsto r^2\, K_1(mr) \in L^1\bigl((0,\infty)\bigr).$$

**Informal**: Split $(0,\infty) = (0, 1/m] \cup (1/m, \infty)$. Near the origin ($mr \le 1$) the
near-origin bound gives $r^2 K_1(mr) \le \tfrac{C r}{m}$ with $C = \cosh 1 + 2$, dominated by an
integrable linear function. Far out ($mr > 1$) the asymptotic bound gives
$r^2 K_1(mr) \le C' r^2 e^{-mr}$ with $C' = \sinh 1 + 2$, integrable by polynomial-times-exponential
decay. This is the key ingredient for showing the 4D free covariance kernel is $L^1$.

**Proof uses**: [`besselK1_near_origin_bound`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L689),
[`besselK1_asymptotic`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L294),
[`besselK1_pos`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L35),
[`besselK1_continuousOn`](../../../OSforGFF/Legacy/BesselK1Analytics.lean#L195);
`Integrable.mono'`, `integrable_of_isBigO_exp_neg`, `IntegrableOn.union`.

---

*This file has **0** definitions and **6** theorems/lemmas (0 with sorry).*
