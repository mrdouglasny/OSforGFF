# `Dim4Bessel.lean` — Informal Summary

> **Source**: [`OSforGFF/Legacy/Dim4Bessel.lean`](../../OSforGFF/Legacy/Dim4Bessel.lean)
> **Generated**: 2026-07-05 (regenerated from current source)

## Overview

**This is LEGACY, off-graph code.** The file preserves the original four-dimensional analytic
development of the free covariance: the momentum-space propagator $1/(\lVert k\rVert^2 + m^2)$, the
heat-kernel and Schwinger (proper-time) representations, the Bessel-function evaluation, and the
**regulated-covariance program** that established the momentum-space identity by an independent route
(Gaussian regulator + Fubini + uniform bound + $\alpha \to 0^+$ limit) before the dimension-generic
Parseval machinery existed. As the file's own header records, it is superseded in role by the
dimension-generic development and is **not on the root import graph** (`OSforGFF.lean` does not import
it). It depends on `OSforGFF/Legacy/BesselK1Analytics.lean`, so build that file's olean first; it is
then verified in isolation with

    lake env lean OSforGFF/Legacy/Dim4Bessel.lean

The content is preserved (not deleted) because it is genuine proven mathematics — an independent
derivation, not a re-statement of the generic results. Everything is fixed to dimension $d = 4$ via
private shorthands `STDimension := 4`, `SpaceTime4 := SpaceTime 4`, `TestFunctionℂ4 := TestFunctionℂ 4`,
and it legitimately uses 4D-specific constructs (`freeCovariance4`, `freeCovarianceBessel`, closed
$16\pi^2$ heat-kernel coefficients). The named 4D kernel `freeCovarianceBessel` / `freeCovariance4` (with the `rfl` identity
`freeCovariance_dim4_eq`) is no longer consumed by the on-graph library — the live
`Instances/Dim4.lean` instance works directly with the radial profile — so the kernel is defined
here (lines 87–98) for the lemmas that refer to it.

**Supersession map (per the header):** `freePropagatorMomentum(_mathlib)` $\to$ `freePropagatorMom`;
`heatKernelPositionSpace` (+ variants) $\to$ `heatKernelProfile`; `covarianceSchwingerRep` (+
variants) $\to$ `properTimeCovariance` / `schwingerIntegral_eq_besselK1`; the regulated program
$\to$ `Covariance/ParsevalGeneric.lean`; `freeCovarianceKernel4` (+ variants),
`freeCovariance_exponential_bound` $\to$ the generic centered kernel `freeCovarianceKernel`.

## Status

**Main result**: Fully proven (0 sorries — `grep` for `sorry`/`admit` returns none). The headline
is `freeCovariance_regulated_limit_eq_freeCovariance`: the Gaussian-regulated Fourier integral of
$1/(\lVert k\rVert^2 + m^2)$ converges, as $\alpha \to 0^+$, to the 4D Bessel covariance
$\frac{m}{4\pi^2 r}K_1(mr)$. Supporting $L^1$-integrability, polynomial and exponential decay, and
$L^2$-embedding-weight results are also established.

**Length**: 2288 lines, 19 definitions + 60 theorems/lemmas.

---

### [Private 4D shorthands](../../OSforGFF/Legacy/Dim4Bessel.lean#L81) — Definitions *(private abbrev)*

**Lean signature**
```lean
private abbrev STDimension : ℕ := 4
private abbrev SpaceTime4 := SpaceTime 4
private abbrev TestFunctionℂ4 := TestFunctionℂ 4
```

**Informal**: File-local shorthands fixing the spacetime dimension to $4$: the dimension `4`, the
Euclidean spacetime `SpaceTime 4`, and the complex test-function space `TestFunctionℂ 4`.

---

### [`schwartz_L2_integrable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L92) — Lemma

**Statement**: Any complex Schwartz function on $\mathbb{R}^4$ has integrable squared norm:
$k \mapsto \lVert f(k)\rVert^2$ is integrable.

**Proof uses**: `SchwartzMap.memLp` (Schwartz $\subseteq L^p$), `memLp_two_iff_integrable_sq_norm`.

---

### [`integral_const_mul`](../../OSforGFF/Legacy/Dim4Bessel.lean#L102) — Theorem

**Statement**: For a measure $\mu$, constant $c \in \mathbb{R}$ and integrable $f$, the scaled
function $x \mapsto c\, f(x)$ is integrable.

**Proof uses**: `MeasureTheory.Integrable.const_mul`.

---

### [`freePropagatorMomentum`](../../OSforGFF/Legacy/Dim4Bessel.lean#L128) — Definition

**Lean signature**
```lean
def freePropagatorMomentum (m : ℝ) (k : SpaceTime4) : ℝ :=
  1 / (‖k‖^2 + m^2)
```

**Informal**: The free momentum-space propagator $1/(\lVert k\rVert^2 + m^2)$ (physics
normalization), the Fourier transform of the free covariance.

---

### [`freePropagator_even`](../../OSforGFF/Legacy/Dim4Bessel.lean#L132) — Lemma

**Statement**: The propagator is even: $P_m(-k) = P_m(k)$ (it depends only on $\lVert k\rVert$).

**Proof uses**: `norm_neg`.

---

### [`freePropagatorMomentum_mathlib`](../../OSforGFF/Legacy/Dim4Bessel.lean#L140) — Definition

**Lean signature**
```lean
noncomputable def freePropagatorMomentum_mathlib (m : ℝ) (k : SpaceTime4) : ℝ :=
  1 / ((2 * Real.pi)^2 * ‖k‖^2 + m^2)
```

**Informal**: The propagator in Mathlib's Fourier convention, $1/((2\pi)^2\lVert k\rVert^2 + m^2)$,
which equals $P_{\mathrm{phys}}(2\pi k)$.

---

### [`freePropagatorMomentum_mathlib_pos`](../../OSforGFF/Legacy/Dim4Bessel.lean#L144) / [`_nonneg`](../../OSforGFF/Legacy/Dim4Bessel.lean#L153) — Lemmas

**Statement**: For $m > 0$, the Mathlib-convention propagator is positive
($0 < P^{\mathrm{ml}}_m(k)$) and hence nonnegative.

**Proof uses**: `div_pos`, `positivity`.

---

### [`freeCovariance_regulated`](../../OSforGFF/Legacy/Dim4Bessel.lean#L168) — Definition

**Lean signature**
```lean
noncomputable def freeCovariance_regulated (α : ℝ) (m : ℝ) (x y : SpaceTime4) : ℝ :=
  let normalisation : ℝ := (2 * Real.pi) ^ STDimension
  let regulator : SpaceTime4 → ℝ := fun k => Real.exp (-α * ‖k‖^2)
  let phase : SpaceTime4 → ℂ := fun k =>
    Complex.exp (-Complex.I * Complex.ofReal (⟪k, x - y⟫_ℝ))
  let amplitude : SpaceTime4 → ℂ := fun k =>
    Complex.ofReal (regulator k * freePropagatorMomentum m k / normalisation)
  (∫ k : SpaceTime4, amplitude k * phase k).re
```

**Informal**: The Gaussian-regulated free covariance in position space,
$$C_\alpha(x,y) = \mathrm{Re}\int \frac{d^4 k}{(2\pi)^4}\;
\frac{e^{-\alpha\lVert k\rVert^2}\, e^{-i\,k\cdot(x-y)}}{\lVert k\rVert^2 + m^2}.$$
The regulator $e^{-\alpha\lVert k\rVert^2}$ ($\alpha > 0$) makes the integral absolutely convergent;
the $\alpha \to 0^+$ limit recovers the Bessel form.

---

### [`schwingerIntegrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L201) — Definition

**Lean signature**
```lean
noncomputable def schwingerIntegrand (t : ℝ) (m : ℝ) (k : SpaceTime4) : ℝ :=
  Real.exp (-t * (‖k‖^2 + m^2))
```

**Informal**: The proper-time integrand $e^{-t(\lVert k\rVert^2 + m^2)}$; integrating over
$t \in (0,\infty)$ recovers $1/(\lVert k\rVert^2 + m^2)$.

---

### [`schwinger_representation`](../../OSforGFF/Legacy/Dim4Bessel.lean#L207) — Theorem

**Statement**: For $m > 0$, the Schwinger (proper-time) identity holds:
$$\int_0^\infty e^{-t(\lVert k\rVert^2 + m^2)}\, dt = \frac{1}{\lVert k\rVert^2 + m^2}.$$

**Proof uses**: `integral_exp_neg_mul_Ioi_eq_inv`.

---

### [`schwingerGaussian`](../../OSforGFF/Legacy/Dim4Bessel.lean#L217) — Definition

**Lean signature**
```lean
noncomputable def schwingerGaussian (α t : ℝ) (m : ℝ) (k : SpaceTime4) : ℝ :=
  Real.exp (-(α + t) * ‖k‖^2 - t * m^2)
```

**Informal**: The combined Gaussian factor $e^{-(\alpha+t)\lVert k\rVert^2 - t m^2}$ merging the
propagator's Schwinger factor with the UV regulator.

---

### [`heatKernelPositionSpace`](../../OSforGFF/Legacy/Dim4Bessel.lean#L223) — Definition

**Lean signature**
```lean
noncomputable def heatKernelPositionSpace (t : ℝ) (r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(STDimension : ℝ) / 2) * Real.exp (-r^2 / (4 * t))
```

**Informal**: The $d$-dimensional position-space heat kernel
$(4\pi t)^{-d/2} e^{-r^2/(4t)}$ — the Fourier transform of the Gaussian $e^{-t\lVert k\rVert^2}$.

---

### [`heatKernelPositionSpace_4D`](../../OSforGFF/Legacy/Dim4Bessel.lean#L227) — Lemma

**Statement**: For $t > 0$ (and $d = 4$),
$$H(t,r) = \frac{1}{16\pi^2 t^2}\, e^{-r^2/(4t)}.$$

**Proof uses**: `Real.rpow_neg`, `Real.rpow_two`, `field_simp`.

---

### [`heatKernelPositionSpace_nonneg`](../../OSforGFF/Legacy/Dim4Bessel.lean#L243) — Lemma

**Statement**: $0 \le H(t,r)$ for $t > 0$.

**Proof uses**: `Real.rpow_nonneg`, `Real.exp_nonneg`.

---

### [`heatKernelPositionSpace_continuous_at`](../../OSforGFF/Legacy/Dim4Bessel.lean#L253) — Lemma

**Statement**: For $t > 0$, $s \mapsto H(s,r)$ is continuous at $t$.

**Proof uses**: `ContinuousAt.rpow`, `ContinuousAt.div`, continuity of `Real.exp`.

---

### [`heatKernelPositionSpace_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L269) — Lemma

**Statement**: For $r > 0$ there is $C > 0$ with $H(s,r) \le C$ for all $s > 0$.

**Informal**: Substituting $u = 1/s$ turns the kernel into $\tfrac{1}{16\pi^2}u^2 e^{-(r^2/4)u}$,
bounded via $u^2 e^{-cu} \le (2/c)^2$; the explicit bound is $4/(\pi^2 r^4) + 1$.

**Proof uses**: `ProbabilityTheory.rpow_abs_le_mul_exp_abs`, `field_simp`.

---

### [`heatKernelPositionSpace_integral_eq_one`](../../OSforGFF/Legacy/Dim4Bessel.lean#L359) — Theorem

**Statement**: The heat kernel has unit mass:
$$\int_{\mathbb{R}^4} H(t, \lVert z\rVert)\, dz = 1 \qquad (t > 0).$$

**Proof uses**: `GaussianFourier.integral_rexp_neg_mul_sq_norm` (with $b = 1/(4t)$),
`finrank_euclideanSpace_fin`, `integral_const_mul`.

---

### [`covarianceSchwingerRep`](../../OSforGFF/Legacy/Dim4Bessel.lean#L399) — Definition

**Lean signature**
```lean
noncomputable def covarianceSchwingerRep (m : ℝ) (r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace t r
```

**Informal**: The position-space covariance as a 1D proper-time integral
$\int_0^\infty e^{-t m^2} H(t,r)\, dt$.

---

### [`covarianceSchwingerRep_4D`](../../OSforGFF/Legacy/Dim4Bessel.lean#L404) — Lemma

**Statement**: In 4D,
$$C(r) = \frac{1}{16\pi^2}\int_0^\infty e^{-t m^2}\,\frac{1}{t^2}\, e^{-r^2/(4t)}\, dt.$$

**Proof uses**: [`heatKernelPositionSpace_4D`](../../OSforGFF/Legacy/Dim4Bessel.lean#L227),
`setIntegral_congr_fun`, `integral_const_mul`.

---

### [`covarianceSchwingerRep_eq_besselFormula`](../../OSforGFF/Legacy/Dim4Bessel.lean#L424) — Theorem

**Statement**: The Schwinger representation equals the explicit Bessel formula:
$$C(r) = \frac{m}{4\pi^2 r}\, K_1(mr) \qquad (m, r > 0).$$

**Informal**: The main link between the proper-time representation and the closed-form 4D scalar
propagator.

**Proof uses**: [`covarianceSchwingerRep_4D`](../../OSforGFF/Legacy/Dim4Bessel.lean#L404),
`schwingerIntegral_eq_besselK1` (order $\nu = -1$ master identity, imported from `General/BesselK`).

---

### [`freeCovarianceBessel_symm`](../../OSforGFF/Legacy/Dim4Bessel.lean#L448) — Lemma

**Statement**: The Bessel covariance is symmetric:
$C_{\mathrm{Bessel}}(x,y) = C_{\mathrm{Bessel}}(y,x)$.

**Proof uses**: `norm_sub_rev` (the `freeCovarianceBessel` kernel defined earlier in this file).

---

### [`freeCovarianceBessel_pos`](../../OSforGFF/Legacy/Dim4Bessel.lean#L454) — Lemma

**Statement**: For $m > 0$ and $x \neq y$, $0 < C_{\mathrm{Bessel}}(x,y)$.

**Proof uses**: `besselK1_pos`, positivity of $\frac{m}{4\pi^2\lVert x-y\rVert}$, `norm_sub_pos_iff`.

---

### [`covarianceSchwingerRegulated`](../../OSforGFF/Legacy/Dim4Bessel.lean#L492) — Definition

**Lean signature**
```lean
noncomputable def covarianceSchwingerRegulated (α : ℝ) (m : ℝ) (r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m^2) * heatKernelPositionSpace (α + t) r
```

**Informal**: The Schwinger-regulated covariance $\int_0^\infty e^{-t m^2} H(\alpha + t, r)\, dt$,
an intermediate form between the Fourier representation and the Bessel form.

---

### [`integrableOn_exp_neg_mul_sq_Ioi`](../../OSforGFF/Legacy/Dim4Bessel.lean#L496) / [`_const_Ioi`](../../OSforGFF/Legacy/Dim4Bessel.lean#L505) — Lemmas

**Statement**: For $m > 0$, $t \mapsto e^{-t m^2}$ (and its scaling by any constant $C$) is
integrable on $(0,\infty)$.

**Proof uses**: `integrableOn_exp_mul_Ioi`, `IntegrableOn.mul_const`.

---

### [`gaussianFT_eq_heatKernel_times_norm`](../../OSforGFF/Legacy/Dim4Bessel.lean#L513) — Lemma

**Statement**: The Gaussian Fourier transform yields the heat kernel (times normalization):
$$\int_{\mathbb{R}^4} e^{-s\lVert k\rVert^2}\, e^{-i\,k\cdot z}\, dk
= (2\pi)^4\, H(s, \lVert z\rVert) \qquad (s > 0).$$

**Proof uses**: `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`,
[`heatKernelPositionSpace_4D`](../../OSforGFF/Legacy/Dim4Bessel.lean#L227),
`finrank_euclideanSpace_fin`, complex-real coercion lemmas.

---

### [`integrable_schwinger_fourier_integrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L596) — Theorem

**Statement**: For $\alpha, m > 0$, the joint integrand
$$p = (k, t) \mapsto \mathbf{1}_{t > 0}\; e^{-(\alpha + t)\lVert k\rVert^2 - t m^2}$$
is integrable on $\mathbb{R}^4 \times \mathbb{R}$ (with the product measure), justifying Tonelli.

**Proof uses**: domination by $g(k)h(t) = e^{-\alpha\lVert k\rVert^2}\cdot
\mathbf{1}_{t>0}e^{-t m^2}$; `Integrable.mul_prod`, Gaussian integrability
(`GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace`), `Integrable.mono'`.

---

### [`fubini_schwinger_integrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L707) — Theorem

**Statement**: For $\alpha, m > 0$ and $x \neq y$, the integration order of the Gaussian $\times$
phase integrand can be swapped:
$$\mathrm{Re}\!\int_k \Bigl(\!\int_t e^{-(\alpha+t)\lVert k\rVert^2}e^{-t m^2}\Bigr)\varphi(k)\,dk
= \int_t e^{-t m^2}\,\mathrm{Re}\!\int_k e^{-(\alpha+t)\lVert k\rVert^2}\varphi(k)\,dk,$$
where $\varphi(k) = e^{-i\,k\cdot(x-y)}$ has unit norm.

**Proof uses**: [`integrable_schwinger_fourier_integrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L596),
`MeasureTheory.integral_integral_swap`, `integral_re`, `norm_exp_neg_I_mul_real`.

---

### [`fubini_schwinger_fourier`](../../OSforGFF/Legacy/Dim4Bessel.lean#L802) — Theorem

**Statement**: The regulated Fourier covariance equals the Schwinger-regulated form:
$$C_\alpha(x,y) = C^{\mathrm{Schwinger}}_\alpha(m, \lVert x - y\rVert) \qquad (\alpha, m > 0,\; x \neq y).$$

**Informal**: Combines the Schwinger representation of the propagator, Fubini's theorem, and the
Gaussian Fourier transform (heat-kernel identity), with the $(2\pi)^4$ normalization cancelling.

**Proof uses**: [`schwinger_representation`](../../OSforGFF/Legacy/Dim4Bessel.lean#L207),
[`gaussianFT_eq_heatKernel_times_norm`](../../OSforGFF/Legacy/Dim4Bessel.lean#L513),
[`integrable_schwinger_fourier_integrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L596),
[`fubini_schwinger_integrand`](../../OSforGFF/Legacy/Dim4Bessel.lean#L707).

---

### [`covarianceSchwingerRegulated_tendsto`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1077) — Lemma

**Statement**: As $\alpha \to 0^+$ the regulated Schwinger covariance converges to the unregulated
one:
$$\lim_{\alpha \to 0^+} C^{\mathrm{Schwinger}}_\alpha(m, r) = C^{\mathrm{Schwinger}}(m, r) \qquad (m, r > 0).$$

**Proof uses**: `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` with dominator
$e^{-t m^2}\cdot C$; [`heatKernelPositionSpace_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L269),
[`heatKernelPositionSpace_continuous_at`](../../OSforGFF/Legacy/Dim4Bessel.lean#L253).

---

### [`covarianceSchwingerRep_eq_freeCovarianceBessel`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1135) — Lemma

**Statement**: The unregulated Schwinger form equals the Bessel covariance:
$$C^{\mathrm{Schwinger}}(m, \lVert x - y\rVert) = C_{\mathrm{Bessel}}(x, y) \qquad (m > 0,\; x \neq y).$$

**Proof uses**: [`covarianceSchwingerRep_eq_besselFormula`](../../OSforGFF/Legacy/Dim4Bessel.lean#L424),
definition of `freeCovarianceBessel`.

---

### [`freeCovariance_regulated_tendsto_bessel`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1147) — Theorem

**Statement**: The regulated Fourier covariance converges to the Bessel form:
$$\lim_{\alpha \to 0^+} C_\alpha(x, y) = C_{\mathrm{Bessel}}(x, y) \qquad (m > 0,\; x \neq y).$$

**Proof uses**: [`covarianceSchwingerRegulated_tendsto`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1077),
[`covarianceSchwingerRep_eq_freeCovarianceBessel`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1135),
[`fubini_schwinger_fourier`](../../OSforGFF/Legacy/Dim4Bessel.lean#L802); `Tendsto.congr'`.

---

### [`freeCovariance_regulated_limit_eq_freeCovariance`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1180) — Theorem

**Statement**: The deep result — the regulated Fourier integral converges to the live 4D covariance:
$$\lim_{\alpha \to 0^+} C_\alpha(x, y) = C_4^{\mathrm{free}}(x, y) \qquad (m > 0,\; x \neq y),$$
i.e. the Fourier transform of $1/(\lVert k\rVert^2 + m^2)$ in 4D equals $\frac{m}{4\pi^2 r}K_1(mr)$.

**Proof uses**: [`freeCovariance_regulated_tendsto_bessel`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1147)
(since `freeCovariance4 = freeCovarianceBessel`).

---

### [`covarianceSchwingerRegulated_le_const_mul`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1196) — Lemma

**Statement**: For $0 < \alpha \le 1$ and $m, r > 0$, a domination bound holds:
$$C^{\mathrm{Schwinger}}_\alpha(m, r) \le e^{m^2}\, C^{\mathrm{Schwinger}}(m, r).$$

**Informal**: Change of variables $s = \alpha + t$ gives an $e^{\alpha m^2}$ prefactor times an
integral over $(\alpha, \infty)$; monotonicity (nonnegative integrand) extends to $(0,\infty)$, and
$e^{\alpha m^2} \le e^{m^2}$ for $\alpha \le 1$.

**Proof uses**: `MeasurePreserving.setIntegral_preimage_emb` (translation),
`setIntegral_mono_set`, [`heatKernelPositionSpace_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L269),
`Real.exp_le_exp_of_le`.

---

### [`freeCovariance_regulated_le_const_mul_freeCovariance`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1301) — Lemma

**Statement**: For $0 < \alpha \le 1$ and $x \neq y$, the regulated covariance is dominated by the
Bessel form:
$$\lvert C_\alpha(x, y)\rvert \le e^{m^2}\, C_4^{\mathrm{free}}(x, y).$$
This enables dominated convergence for the bilinear form.

**Proof uses**: [`fubini_schwinger_fourier`](../../OSforGFF/Legacy/Dim4Bessel.lean#L802),
[`covarianceSchwingerRegulated_le_const_mul`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1196),
[`covarianceSchwingerRep_eq_freeCovarianceBessel`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1135).

---

### [`gaussian_regulator_integrable'`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1325) — Lemma

**Statement**: For $\alpha > 0$, the Gaussian regulator $k \mapsto e^{-\alpha\lVert k\rVert^2}$ is
integrable on $\mathbb{R}^4$.

**Proof uses**: `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add`, real-part extraction.

---

### [`freeCovariance_regulated_uniformly_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1347) — Lemma

**Statement**: For $\alpha, m > 0$ there is $M > 0$ with
$\lvert C_\alpha(x, y)\rvert \le M$ for all $x, y$, namely
$M = \int e^{-\alpha\lVert k\rVert^2}/(m^2 (2\pi)^4)\, dk$.

**Informal**: Since $\lvert$phase$\rvert = 1$ and the propagator is $\le 1/m^2$, the amplitude is
bounded by $e^{-\alpha\lVert k\rVert^2}/(m^2(2\pi)^4)$, whose integral is finite.

**Proof uses**: `Complex.abs_re_le_norm`, `norm_integral_le_integral_norm`,
`norm_exp_neg_I_mul_real`, [`gaussian_regulator_integrable'`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1325).

---

### [`aestronglyMeasurable_freeCovariance_regulated`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1432) — Lemma

**Statement**: The complex-lifted regulated covariance
$p \mapsto (C_\alpha(p_1, p_2) : \mathbb{C})$ is a.e.-strongly-measurable on the product space.

**Informal**: It is in fact continuous in $(x,y)$ via dominated continuity, the integrand being
continuous in $(x,y)$ with $(x,y)$-independent dominator $e^{-\alpha\lVert k\rVert^2}/m^2$.

**Proof uses**: `MeasureTheory.continuous_of_dominated`, continuity/positivity of
`freePropagatorMomentum`, `norm_exp_neg_I_mul_real`.

---

### [`aestronglyMeasurable_freeCovariance`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1512) — Lemma

**Statement**: The complex-lifted Bessel covariance $p \mapsto (C_4^{\mathrm{free}}(p_1, p_2) :
\mathbb{C})$ is a.e.-strongly-measurable on the product space (for `[Fact (0 < m)]`).

**Informal**: Continuous off the diagonal, which is conull (the diagonal has product measure zero),
then lifted to the full space.

**Proof uses**: `Measure.measure_prod_null_of_ae_null`, `measure_singleton`,
`besselK1_continuousOn`, `ContinuousOn.aestronglyMeasurable`.

---

### [`freeCovariance_regulated_bilinear_integrable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1597) — Theorem

**Statement**: For $\alpha > 0$ and Schwartz $f, g$, the bilinear integrand
$p \mapsto f(p_1)\, C_\alpha(p_1, p_2)\, g(p_2)$ is integrable on $\mathbb{R}^4 \times \mathbb{R}^4$.

**Proof uses**: uniform bound
[`freeCovariance_regulated_uniformly_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1347),
domination by $M\lVert f(x)\rVert\lVert g(y)\rVert$; `SchwartzMap.integrable`,
`Integrable.mul_prod`, `Integrable.mono'`,
[`aestronglyMeasurable_freeCovariance_regulated`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1432).

---

### [`freeCovarianceKernel4`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1653) — Definition

**Lean signature**
```lean
noncomputable def freeCovarianceKernel4 (m : ℝ) (z : SpaceTime4) : ℝ :=
  freeCovariance4 m 0 z
```

**Informal**: The translation-invariant covariance kernel $K(z) = C_4^{\mathrm{free}}(0, z)$.

---

### [`freeCovarianceKernel4_integrable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1662) — Lemma

**Statement**: For $m > 0$, the kernel $K$ is $L^1$ on $\mathbb{R}^4$.

**Informal**: As a radial function, $\int_{\mathbb{R}^4}\lvert K\rvert
\leftrightarrow \frac{m}{4\pi^2}\int_0^\infty r^2 K_1(mr)\, dr$, finite by
`radial_besselK1_integrable`.

**Proof uses**: `integrable_fun_norm_addHaar`, `finrank_euclideanSpace`,
[`radial_besselK1_integrable`](../../OSforGFF/Legacy/BesselK1Analytics.lean#L702).

---

### [`freeCovarianceKernel4_decay_bound`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1695) — Lemma

**Statement**: There is $C > 0$ with a polynomial (inverse-square) decay bound
$$\lvert K(z)\rvert \le C\,\lVert z\rVert^{-2} \qquad (\text{all } z),\qquad C = \frac{\cosh 1 + 2}{4\pi^2}.$$

**Informal**: Near the origin ($mr \le 1$) uses $K_1(mr) \le (\cosh 1 + 2)/(mr)$; far out ($mr > 1$)
uses $e^{-mr} \le 1/(mr)$ and $K_1(mr) \le (\sinh 1 + 2)e^{-mr}$, with $\sinh 1 < \cosh 1$. Essential
for OS1 local integrability in 4D.

**Proof uses**: [`besselK1_near_origin_bound`](../../OSforGFF/Legacy/BesselK1Analytics.lean#L689),
[`besselK1_asymptotic`](../../OSforGFF/Legacy/BesselK1Analytics.lean#L294), `add_one_le_exp`,
`inv_anti₀`.

---

### [`freeCovariance_exponential_bound`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1852) — Lemma

**Statement**: For $m > 0$ and $m\lVert u - v\rVert \ge 1$, the covariance decays exponentially:
$$\lvert C_4^{\mathrm{free}}(u, v)\rvert \le \frac{m^2(\sinh 1 + 2)}{4\pi^2}\, e^{-m\lVert u - v\rVert}.$$

**Informal**: Combines $C(u,v) = \frac{m}{4\pi^2 r}K_1(mr)$, the asymptotic
$K_1(z) \le (\sinh 1 + 2)e^{-z}$, and $m/r \le m^2$ (from $mr \ge 1$).

**Proof uses**: [`freeCovarianceBessel_pos`](../../OSforGFF/Legacy/Dim4Bessel.lean#L454),
[`besselK1_asymptotic`](../../OSforGFF/Legacy/BesselK1Analytics.lean#L294).

---

### [`freeCovariance_exponential_bound'`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1913) — Lemma

**Statement**: The same exponential decay bound, stated with `[Fact (0 < m)]` instead of an explicit
hypothesis $m > 0$ (a convenience wrapper).

**Proof uses**: [`freeCovariance_exponential_bound`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1852),
`Fact.out`.

---

### [`freeCovarianceKernel4_continuousOn`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1928) — Lemma

**Statement**: For $m > 0$, the kernel $K$ is continuous on $\{z \mid z \neq 0\}$.

**Informal**: $K(z) = f(\lVert z\rVert)$ with $f(r) = \frac{m}{4\pi^2 r}K_1(mr)$ continuous on
$(0,\infty)$; composing with $\lVert\cdot\rVert$ (nonzero off the origin) gives continuity. Essential
for the double-mollifier convergence theorem.

**Proof uses**: `besselK1_continuousOn`, `ContinuousOn.comp`, `ContinuousOn.congr`.

---

### [`freeCovarianceℂ_bilinear_integrable'`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1968) — Theorem

**Statement**: For Schwartz $f, g$, the bilinear integrand
$p \mapsto f(p_1)\, C_4^{\mathrm{free}}(p_1, p_2)\, g(p_2)$ is integrable, using $L^1$-ness of the
translation-invariant Bessel kernel.

**Proof uses**: translation invariance $C_4(x,y) = K(x - y)$,
[`freeCovarianceKernel4_integrable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1662),
`schwartz_bilinear_integrable_of_translationInvariant_L1`.

---

### [`negSpaceTime`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1985) — Definition

**Lean signature**
```lean
def negSpaceTime : SpaceTime4 ≃ₗᵢ[ℝ] SpaceTime4 where
  toLinearEquiv := LinearEquiv.neg ℝ
  norm_map' := norm_neg
```

**Informal**: Negation $k \mapsto -k$ as a linear isometry equivalence on `SpaceTime4`.

---

### [`integral_comp_neg_spacetime`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1991) — Theorem

**Statement**: Reflection invariance of the integral: $\int_k f(-k) = \int_k f(k)$ for any
$E$-valued $f$ on `SpaceTime4`.

**Proof uses**: [`negSpaceTime`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1985),
`LinearIsometryEquiv.measurePreserving`, `MeasurePreserving.integral_comp`.

---

### [`freeCovariance_symmetric`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1998) — Lemma

**Statement**: $C_4^{\mathrm{free}}(x, y) = C_4^{\mathrm{free}}(y, x)$.

**Proof uses**: [`freeCovarianceBessel_symm`](../../OSforGFF/Legacy/Dim4Bessel.lean#L448).

---

### [`freeCovariance_star`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2003) / [`freeCovariance_hermitian`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2008) — Lemmas *(simp)*

**Statement**: The complex-lifted position-space kernel is real-valued
($\mathrm{star}(C_4(x,y)) = C_4(x,y)$) and Hermitian
($C_4(x,y) = \mathrm{star}(C_4(y,x))$).

**Proof uses**: `simp`; [`freeCovariance_symmetric`](../../OSforGFF/Legacy/Dim4Bessel.lean#L1998).

---

### [`freePropagator_smooth`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2014) / [`freePropagator_complex_smooth`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2033) — Lemmas

**Statement**: For `[Fact (0 < m)]`, the propagator $k \mapsto 1/(\lVert k\rVert^2 + m^2)$ (and its
$\mathbb{C}$-coercion) is $C^\infty$ (`ContDiff ℝ ⊤`).

**Proof uses**: `ContDiff.div`, `contDiff_norm_sq`, `ofRealCLM.contDiff`; nonvanishing denominator.

---

### [`freePropagator_pos`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2047) / [`freePropagator_bounded`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2056) / [`freePropagator_continuous`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2067) — Lemmas

**Statement**: For `[Fact (0 < m)]`: the propagator is positive ($0 < P_m(k)$), bounded above by
$1/m^2$, and continuous.

**Proof uses**: `div_pos`, `div_le_div_of_nonneg_left`, `Continuous.div` with nonvanishing
denominator.

---

### [`freePropagatorMomentum_star`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2096) / [`_starRing`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2101) / [`_im`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2106) — Lemmas *(simp)*

**Statement**: The momentum-space propagator is real-valued: its complex conjugate (via `star` and
via `starRingEnd ℂ`) equals itself, and its imaginary part vanishes.

**Proof uses**: `simp`.

---

### [`momentumWeight`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2113) / [`momentumWeight_mathlib`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2118) — Definitions

**Lean signature**
```lean
noncomputable def momentumWeight (m : ℝ) (k : SpaceTime4) : ℝ := 1 / (‖k‖^2 + m^2)
noncomputable def momentumWeight_mathlib (m : ℝ) (k : SpaceTime4) : ℝ :=
  freePropagatorMomentum_mathlib m k
```

**Informal**: The momentum-space weight $1/(\lVert k\rVert^2 + m^2)$ (physics convention) and its
Mathlib-convention counterpart $1/((2\pi)^2\lVert k\rVert^2 + m^2)$.

---

### [`momentumWeightSqrt`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2122) / [`momentumWeightSqrt_mathlib`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2127) — Definitions

**Lean signature**
```lean
noncomputable def momentumWeightSqrt (m : ℝ) (k : SpaceTime4) : ℝ :=
  1 / Real.sqrt (‖k‖^2 + m^2)
noncomputable def momentumWeightSqrt_mathlib (m : ℝ) (k : SpaceTime4) : ℝ :=
  1 / Real.sqrt ((2 * Real.pi)^2 * ‖k‖^2 + m^2)
```

**Informal**: The square-root momentum weights $1/\sqrt{\lVert k\rVert^2 + m^2}$ (physics) and
$1/\sqrt{(2\pi)^2\lVert k\rVert^2 + m^2}$ (Mathlib), used to build the $L^2$ embedding of the
covariance.

---

### [`momentumWeightSqrt_mathlib_pos`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2131) / [`_sq`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2142) — Lemmas

**Statement**: For `[Fact (0 < m)]`: the Mathlib sqrt weight is positive, and its square recovers the
weight: $(W^{1/2}_{\mathrm{ml}}(k))^2 = W_{\mathrm{ml}}(k)$.

**Proof uses**: `div_pos`, `Real.sqrt_pos`, `Real.sq_sqrt`.

---

### [`momentumWeightSqrt_continuous`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2152) / [`momentumWeightSqrt_mathlib_continuous`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2168) — Lemmas

**Statement**: For `[Fact (0 < m)]`, both sqrt weight functions are continuous.

**Proof uses**: `Continuous.div` with nonvanishing $\sqrt{\cdot}$, `Continuous.sqrt`.

---

### [`momentumWeightSqrt_measurable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2184) / [`momentumWeightSqrt_mathlib_measurable`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2189) — Lemmas

**Statement**: For `[Fact (0 < m)]`, both sqrt weight functions are measurable.

**Proof uses**: `Continuous.measurable` applied to the continuity lemmas above.

---

### [`momentumWeightSqrt_bounded_ae`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2194) / [`momentumWeightSqrt_mathlib_bounded_ae`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2218) — Lemmas

**Statement**: For `[Fact (0 < m)]`, the $\mathbb{C}$-lifted sqrt weights are a.e. bounded by $1/m$:
$\lVert (W^{1/2}(k) : \mathbb{C})\rVert \le 1/m$.

**Proof uses**: $m \le \sqrt{\lVert k\rVert^2 + m^2}$ (`Real.sqrt_sq`, `Real.sqrt_le_sqrt`),
`one_div_le_one_div_of_le`.

---

### [`momentumWeightSqrt_mul_CLM`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2244) / [`momentumWeightSqrt_mathlib_mul_CLM`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2257) — Definitions

**Lean signature**
```lean
noncomputable def momentumWeightSqrt_mul_CLM (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure SpaceTime4) →L[ℂ] Lp ℂ 2 (volume : Measure SpaceTime4)
```

**Informal**: Multiplication by the (complex-lifted) square-root momentum weight, as a bounded linear
operator on complex $L^2(\mathbb{R}^4)$ (with $\lVert\cdot\rVert_\infty \le 1/m$), in both physics and
Mathlib conventions. Built via `linfty_mul_L2_CLM` from the measurability and a.e. boundedness lemmas.

---

### [`momentumWeightSqrt_mathlib_mul_CLM_spec`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2268) — Lemma

**Statement**: The Mathlib multiplication operator acts a.e. by pointwise multiplication:
$(W^{1/2}_{\mathrm{ml}}\!\cdot)\, f =_{\text{a.e.}} k \mapsto W^{1/2}_{\mathrm{ml}}(k)\, f(k)$.

**Proof uses**: `linfty_mul_L2_CLM_spec`.

---

### [`momentumWeightSqrt_mathlib_le_inv_mass`](../../OSforGFF/Legacy/Dim4Bessel.lean#L2276) — Lemma

**Statement**: For `[Fact (0 < m)]`, the (real) Mathlib sqrt weight is pointwise bounded:
$W^{1/2}_{\mathrm{ml}}(k) \le 1/m$ for every $k$.

**Proof uses**: $m \le \sqrt{(2\pi)^2\lVert k\rVert^2 + m^2}$, `one_div_le_one_div_of_le`.

---

*This file has **19** definitions and **60** theorems/lemmas (0 with sorry).*
