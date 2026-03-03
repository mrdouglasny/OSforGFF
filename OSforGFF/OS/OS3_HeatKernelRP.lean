/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.OS.OS3_DiagonalRP

/-!
# OS3 — Reflection Positivity via Schwinger/Heat Kernel Factorization

Alternative proof of bilinear-form RP for the free covariance, replacing the
momentum-space argument of `OS3_CovarianceRP` with a real-space heat kernel argument.

## Proof strategy

### Step 1: Off-diagonal Schwinger representation

For positive-time x, y (with Θx ≠ y):

  C(Θx, y) = ∫₀^∞ e^{−sm²} H_s(‖Θx − y‖) ds

This follows from `covarianceSchwingerRep_eq_freeCovarianceBessel` and the definition
of `covarianceSchwingerRep`.

### Step 2: Heat kernel factorization

The key geometric identity: for positive-time x, y,

  ‖Θx − y‖² = (x₀ + y₀)² + ‖x̄ − ȳ‖²

because Θ negates the time component.  This factorizes the 4D heat kernel as:

  H_s^{4D}(‖Θx − y‖) = H_s^{1D}(x₀ + y₀) · H_s^{3D}(‖x̄ − ȳ‖)

### Step 3: 1D heat kernel RP (Axiom)

For any Schwartz function g : ℝ → ℂ supported in positive time:

  Re ∫∫ conj(g(t₁)) H_s^{1D}(t₁ + t₂) g(t₂) dt₁ dt₂ ≥ 0

Proof sketch (not yet formalized): the Laplace symbol of the Hankel operator T_s
defined by (T_s g)(t) = ∫₀^∞ H_s^{1D}(t + τ) g(τ) dτ is

  σ(ω) = (1/2) e^{sω²} erfc(ω√s) > 0   for all ω > 0

so by the Hankel operator characterization (Krein's theorem), T_s ≥ 0.

### Step 4: Combining via spatial Fourier + Fubini

For each s > 0:

  Re ∫∫ conj(f(x)) H_s^{4D}(‖Θx − y‖) f(y) dx dy
    = (1/(2π)³) ∫_{k̄} e^{−s|k̄|²} [Re ∫∫_{t₁,t₂>0} conj(F̂(t₁,k̄)) H_s^{1D}(t₁+t₂) F̂(t₂,k̄) dt] dk̄
    ≥ 0

where F̂(t, k̄) = ∫ f(t, x̄) e^{ik̄·x̄} dx̄ (spatial Fourier transform of f).
Each inner integral is ≥ 0 by the 1D axiom; e^{−s|k̄|²} ≥ 0.

Fubini over s then gives the full bilinear form RP.

## Key results

- `heatKernelFactorization`: H_s(‖Θx−y‖) = H_s^{1D}(x₀+y₀) · H_s^{3D}(‖x̄−ȳ‖)
- `freeCovariance_reflection_schwinger_offdiag`: off-diagonal Schwinger rep
- `heatKernel1D_RP`: axiom (Hankel operator positivity)
- `freeCovariance_RP_heat_kernel`: bilinear form RP (main theorem)
-/

open MeasureTheory Real Complex
open scoped BigOperators

noncomputable section

namespace OSforGFF

/-! ## 1D and 3D heat kernels -/

/-- The 1D Gaussian heat kernel: H_s^{1D}(r) = (4πs)^{−1/2} exp(−r²/(4s)). -/
noncomputable def heatKernel1D (s r : ℝ) : ℝ :=
  (4 * Real.pi * s) ^ (-(1 : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * s))

/-- The 3D Gaussian heat kernel: H_s^{3D}(r) = (4πs)^{−3/2} exp(−r²/(4s)). -/
noncomputable def heatKernel3D (s r : ℝ) : ℝ :=
  (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * s))

lemma heatKernel1D_nonneg (s : ℝ) (hs : 0 < s) (r : ℝ) : 0 ≤ heatKernel1D s r := by
  unfold heatKernel1D
  apply mul_nonneg
  · positivity
  · positivity

lemma heatKernel3D_nonneg (s : ℝ) (hs : 0 < s) (r : ℝ) : 0 ≤ heatKernel3D s r := by
  unfold heatKernel3D
  apply mul_nonneg
  · positivity
  · positivity

/-- The 4D heat kernel is the product of the 1D and 3D heat kernels at the same scale. -/
lemma heatKernelPositionSpace_eq_product (s : ℝ) (hs : 0 < s) (r₁ r₂ : ℝ) :
    heatKernelPositionSpace s (Real.sqrt (r₁ ^ 2 + r₂ ^ 2)) =
    heatKernel1D s r₁ * heatKernel3D s r₂ := by
  unfold heatKernelPositionSpace heatKernel1D heatKernel3D
  simp only [STDimension, Nat.cast_ofNat]
  have h_base : (0 : ℝ) < 4 * Real.pi * s := by positivity
  have h_sq : Real.sqrt (r₁ ^ 2 + r₂ ^ 2) ^ 2 = r₁ ^ 2 + r₂ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [show -(4 : ℝ) / 2 = -(1 : ℝ) / 2 + -(3 : ℝ) / 2 by norm_num,
      Real.rpow_add h_base, h_sq,
      show -(r₁ ^ 2 + r₂ ^ 2) / (4 * s) = -r₁ ^ 2 / (4 * s) + (-r₂ ^ 2 / (4 * s)) by ring,
      Real.exp_add]
  ring

/-! ## Norm factorization: ‖Θx − y‖² = (x₀ + y₀)² + ‖x̄ − ȳ‖² -/

/-- The time component of Θx − y is −(x₀ + y₀). -/
lemma timeReflection_sub_time (x y : SpaceTime) :
    (QFT.timeReflection x - y) 0 = -(x 0 + y 0) := by
  simp only [PiLp.sub_apply, QFT.timeReflection, WithLp.equiv_symm_apply,
             Function.update_self]
  ring

/-- Spatial components of Θx − y equal those of x − y. -/
lemma timeReflection_sub_spatial (x y : SpaceTime) (i : Fin STDimension) (hi : i ≠ 0) :
    (QFT.timeReflection x - y) i = x i - y i := by
  simp only [PiLp.sub_apply, QFT.timeReflection, WithLp.equiv_symm_apply,
             Function.update_of_ne hi]

/-- ‖Θx − y‖² = (x₀ + y₀)² + ‖spatialPart x − spatialPart y‖². -/
lemma timeReflection_sub_norm_sq (x y : SpaceTime) :
    ‖QFT.timeReflection x - y‖ ^ 2 =
    (x 0 + y 0) ^ 2 + ‖spatialPart x - spatialPart y‖ ^ 2 := by
  -- Time component: (Θx-y)₀ = -x₀-y₀; spatial components: (Θx-y)ᵢ = xᵢ-yᵢ for i≠0
  -- The norm splits as (x₀+y₀)² + Σᵢ≠₀ (xᵢ-yᵢ)² = (x₀+y₀)² + ‖x̄-ȳ‖²
  sorry

/-! ## Heat kernel factorization at the reflected point -/

/-- The 4D heat kernel at ‖Θx − y‖ factorizes as H_s^{1D}(x₀+y₀) · H_s^{3D}(‖x̄−ȳ‖). -/
theorem heatKernelFactorization (s : ℝ) (hs : 0 < s) (x y : SpaceTime) :
    heatKernelPositionSpace s ‖QFT.timeReflection x - y‖ =
    heatKernel1D s (x 0 + y 0) * heatKernel3D s ‖spatialPart x - spatialPart y‖ := by
  have hnorm : ‖QFT.timeReflection x - y‖ =
      Real.sqrt ((x 0 + y 0) ^ 2 + ‖spatialPart x - spatialPart y‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), timeReflection_sub_norm_sq]
  rw [hnorm, heatKernelPositionSpace_eq_product s hs]

/-! ## Off-diagonal Schwinger representation -/

/-- For positive-time x, y, C(Θx, y) = ∫₀^∞ e^{−sm²} H_s(‖Θx−y‖) ds.

The hypothesis `hx` and `hy` ensure Θx ≠ y (since (Θx)₀ = −x₀ < 0 ≠ y₀). -/
lemma freeCovariance_reflection_schwinger_offdiag (m : ℝ) (hm : 0 < m)
    (x y : SpaceTime) (hx : 0 < x 0) (hy : 0 < y 0) :
    freeCovariance m (QFT.timeReflection x) y =
    ∫ s in Set.Ioi 0, Real.exp (-s * m ^ 2) *
      heatKernelPositionSpace s ‖QFT.timeReflection x - y‖ := by
  have h_time : QFT.timeReflection x 0 = -x 0 := by
    have h := timeReflection_sub_self_apply x 0
    simp only [PiLp.sub_apply, if_true] at h
    linarith
  have h_ne : QFT.timeReflection x ≠ y := by
    intro heq
    have : QFT.timeReflection x 0 = y 0 := by rw [heq]
    linarith [h_time]
  have h := covarianceSchwingerRep_eq_freeCovarianceBessel m hm
      (QFT.timeReflection x) y h_ne
  simp only [covarianceSchwingerRep] at h
  exact h.symm

/-! ## Step 3: 1D heat kernel RP (Axiom) -/

/-- **Axiom**: The 1D heat kernel Hankel operator is positive definite.

For any Schwartz function g : ℝ → ℂ supported on [0, ∞),

  Re ∫∫ conj(g(t₁)) · H_s^{1D}(t₁ + t₂) · g(t₂) dt₁ dt₂ ≥ 0

**Proof sketch** (not yet formalized in Lean):

The Laplace transform of H_s^{1D}(t) on [0,∞) gives the Hankel symbol:
  σ(ω) = ∫₀^∞ H_s^{1D}(t) e^{−ωt} dt = (1/2) e^{sω²} erfc(ω√s)

Since erfc > 0 on ℝ, we have σ(ω) > 0 for all ω > 0. By Krein's theorem on
positive Hankel operators (the Hankel operator Γ_k with kernel k = H_s^{1D}
is positive iff its Laplace symbol σ is nonneg), T_s ≥ 0 on L²(0,∞). -/
axiom heatKernel1D_RP (s : ℝ) (hs : 0 < s)
    (g : SchwartzMap ℝ ℂ) (hg : ∀ t : ℝ, t ≤ 0 → g t = 0) :
    0 ≤ (∫ t₁ : ℝ, ∫ t₂ : ℝ,
      starRingEnd ℂ (g t₁) * (heatKernel1D s (t₁ + t₂) : ℂ) * g t₂).re

/-! ## Step 4: Spacetime bilinear form for each s -/

/-- For each s > 0, the spacetime bilinear form with the 4D heat kernel at ‖Θx−y‖
is nonneg for positive-time test functions.

**Proof** (sorry — requires spatial Fourier transform):
Using F̂(t, k̄) = ∫ f(t, x̄) e^{ik̄·x̄} dx̄:

  Re ∫∫ conj(f(x)) H_s^{4D}(‖Θx−y‖) f(y) dx dy
    = (1/(2π)³) ∫_{k̄} e^{−s|k̄|²} [Re ∫∫ conj(F̂(t₁,k̄)) H_s^{1D}(t₁+t₂) F̂(t₂,k̄) dt] dk̄

Each inner integral is ≥ 0 by `heatKernel1D_RP` applied to the fiber g := F̂(·,k̄).
The outer integral is ≥ 0 since e^{−s|k̄|²} ≥ 0. -/
theorem heatKernelBilinear_nonneg (s : ℝ) (hs : 0 < s)
    (f : TestFunctionℂ) (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    0 ≤ (∫ x : SpaceTime, ∫ y : SpaceTime,
      starRingEnd ℂ (f x) *
      (heatKernelPositionSpace s ‖QFT.timeReflection x - y‖ : ℂ) * f y).re := by
  -- Rewrite using heat kernel factorization
  simp_rw [heatKernelFactorization s hs]
  -- Reduce to 1D RP for each spatial Fourier mode via Parseval + Fubini
  -- (Requires spatial Fourier decomposition; see proof sketch above)
  sorry

/-! ## Main theorem: bilinear form RP -/

/-- **Bilinear form reflection positivity** via the Schwinger/heat kernel route.

  Re ∫∫ conj(f(x)) C(Θx, y) f(y) dx dy ≥ 0

for f supported in positive time.

**Proof structure**:
1. Substitute the off-diagonal Schwinger rep for C(Θx, y).
2. Fubini to bring ∫₀^∞ e^{−sm²} outside.
3. For each s, `heatKernelBilinear_nonneg` gives the inner bilinear form ≥ 0.
4. The outer integral of nonneg things is nonneg. -/
theorem freeCovariance_RP_heat_kernel (m : ℝ) [Fact (0 < m)]
    (f : TestFunctionℂ) (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    0 ≤ (∫ x : SpaceTime, ∫ y : SpaceTime,
      starRingEnd ℂ (f x) * (freeCovariance m (QFT.timeReflection x) y : ℂ) * f y).re := by
  have hm := (Fact.out : 0 < m)
  -- Step 1 + 2: Expand C(Θx,y) via Schwinger rep and bring ∫s outside
  -- (Fubini integrability is deferred)
  have h_fubini :
      (∫ x : SpaceTime, ∫ y : SpaceTime,
        starRingEnd ℂ (f x) * (freeCovariance m (QFT.timeReflection x) y : ℂ) * f y).re =
      (∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * m ^ 2) *
        (∫ x : SpaceTime, ∫ y : SpaceTime,
          starRingEnd ℂ (f x) *
          (heatKernelPositionSpace s ‖QFT.timeReflection x - y‖ : ℂ) * f y).re) := by
    sorry -- Fubini: swap ∫s with ∫x ∫y; requires integrability bounds on f
  rw [h_fubini]
  -- Step 3 + 4: Outer integral of nonneg things is nonneg
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  simp only [Set.mem_Ioi] at hs
  apply mul_nonneg (Real.exp_nonneg _)
  exact heatKernelBilinear_nonneg s hs f hf_supp

end OSforGFF

end
