/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.Spacetime.PositiveTimeTestFunction
import OSforGFF.Covariance.Momentum
import OSforGFF.Covariance.Position
import OSforGFF.OS.OS3_CovarianceRP

/-!
# OS3 — Reflection Positivity via Diagonal Kernel Positivity

New proof strategy, avoiding the spatial Fourier decomposition of the test function.

## Step 1: Distance formula

For any x = (x₀, x̄) ∈ SpaceTime, the reflected point Θx = (−x₀, x̄) satisfies:

  ‖Θx − x‖ = ‖(−2x₀, 0, …, 0)‖ = 2|x₀|

This is independent of the spatial part x̄.

## Step 2: Diagonal kernel positivity

For x in positive time (x₀ > 0):

  C(Θx, x) = ∫₀^∞ e^{−sm²} H_s(2x₀) ds ≥ 0

because H_s ≥ 0 and e^{−sm²} > 0.  The value depends only on x₀, not on x̄.

## Step 3: Bilinear form (to be developed)

  Re ∫∫ f*(x) C(Θx, y) f(y) dx dy ≥ 0

for f supported in positive time.  We keep the 4D integrals over x and y
rather than decomposing f via a spatial Fourier transform.

## Key results

- `timeReflection_sub_self_norm`: ‖Θx − x‖ = 2 * |x₀|
- `freeCovariance_reflection_diagonal_nonneg`: C(Θx, x) ≥ 0 for x₀ > 0
- `freeCovariance_reflection_positive_bilinear_new`: (sorry) bilinear RP
-/

open MeasureTheory Real
open scoped BigOperators

noncomputable section

namespace OSforGFF

/-! ## Step 1: Component formula and distance -/

/-- The i-th component of (Θx − x): time component is −2x₀, spatial components are 0. -/
lemma timeReflection_sub_self_apply (x : SpaceTime) (i : Fin STDimension) :
    (QFT.timeReflection x - x) i = if i = 0 then -2 * x 0 else 0 := by
  simp only [PiLp.sub_apply, QFT.timeReflection, WithLp.equiv_symm_apply,
             Function.update_apply]
  by_cases h : i = 0
  · simp [h]; ring
  · simp [h]

/-- ‖Θx − x‖² = (2x₀)² — only the time component contributes. -/
lemma timeReflection_sub_self_norm_sq (x : SpaceTime) :
    ‖QFT.timeReflection x - x‖ ^ 2 = (2 * x 0) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [timeReflection_sub_self_apply]
  have : ∑ i : Fin STDimension, ‖if i = 0 then -2 * x 0 else (0 : ℝ)‖ ^ 2 =
         ‖(-2 * x 0 : ℝ)‖ ^ 2 := by
    rw [Finset.sum_eq_single (0 : Fin STDimension)]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  rw [this, Real.norm_eq_abs, sq_abs]
  ring

/-- **Key distance formula**: ‖Θx − x‖ = 2 * |x₀|.

The distance from a point to its time reflection depends only on the time
component — not on the spatial part x̄. -/
theorem timeReflection_sub_self_norm (x : SpaceTime) :
    ‖QFT.timeReflection x - x‖ = 2 * |x 0| := by
  have hsq := timeReflection_sub_self_norm_sq x
  have hnn : 0 ≤ ‖QFT.timeReflection x - x‖ := norm_nonneg _
  -- ‖v‖ = sqrt(‖v‖²)
  conv_lhs => rw [← Real.sqrt_sq hnn]
  rw [hsq, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-! ## Step 2: Schwinger representation at the diagonal -/

/-- For positive-time x, the reflected point Θx differs from x. -/
lemma timeReflection_ne_self_of_pos {x : SpaceTime} (hx : 0 < x 0) :
    QFT.timeReflection x ≠ x := by
  intro h_eq
  have h0 := timeReflection_sub_self_apply x 0
  rw [h_eq, sub_self] at h0
  simp only [PiLp.zero_apply, if_true] at h0
  linarith

/-- For positive-time x, C(Θx, x) equals the Schwinger integral ∫₀^∞ e^{−sm²} H_s(2x₀) ds.

The radius ‖Θx − x‖ = 2x₀ is independent of the spatial part x̄. -/
lemma freeCovariance_reflection_eq_schwinger (m : ℝ) (hm : 0 < m) (x : SpaceTime)
    (hx : 0 < x 0) :
    freeCovariance m (QFT.timeReflection x) x =
    ∫ s in Set.Ioi 0, Real.exp (-s * m ^ 2) *
      heatKernelPositionSpace s ‖QFT.timeReflection x - x‖ := by
  have h_ne : QFT.timeReflection x ≠ x := timeReflection_ne_self_of_pos hx
  have h := covarianceSchwingerRep_eq_freeCovarianceBessel m hm (QFT.timeReflection x) x h_ne
  simp only [covarianceSchwingerRep] at h
  exact h.symm

/-- C(Θx, x) depends only on x₀ — it equals covarianceSchwingerRep m (2 * x₀). -/
lemma freeCovariance_reflection_diagonal_eq (m : ℝ) (hm : 0 < m) (x : SpaceTime)
    (hx : 0 < x 0) :
    freeCovariance m (QFT.timeReflection x) x = covarianceSchwingerRep m (2 * x 0) := by
  rw [freeCovariance_reflection_eq_schwinger m hm x hx,
      timeReflection_sub_self_norm, abs_of_pos hx]
  simp [covarianceSchwingerRep]

/-! ## Step 3: Diagonal kernel nonnegativity -/

/-- **C(Θx, x) ≥ 0** for any positive-time point x.

Proof: C(Θx, x) = ∫₀^∞ e^{−sm²} H_s(2x₀) ds.
Both e^{−sm²} ≥ 0 and H_s(r) ≥ 0 (heat kernel), so the integral is nonneg.
The value equals covarianceSchwingerRep m (2x₀), independent of x̄. -/
theorem freeCovariance_reflection_diagonal_nonneg (m : ℝ) (hm : 0 < m) (x : SpaceTime)
    (hx : 0 < x 0) :
    0 ≤ freeCovariance m (QFT.timeReflection x) x := by
  rw [freeCovariance_reflection_eq_schwinger m hm x hx]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro s hs
  exact mul_nonneg (Real.exp_nonneg _)
    (heatKernelPositionSpace_nonneg s (Set.mem_Ioi.mp hs) _)

/-! ## Step 4: Euclidean normalization to axis form -/

/-- The point (t, 0, 0, 0) on the time axis. -/
noncomputable def onTimeAxis (t : ℝ) : SpaceTime :=
  (WithLp.equiv 2 (Fin STDimension → ℝ)).symm (Pi.single 0 t)

@[simp] lemma onTimeAxis_apply (t : ℝ) (i : Fin STDimension) :
    onTimeAxis t i = if i = 0 then t else 0 := by
  simp [onTimeAxis, WithLp.equiv_symm_apply]

@[simp] lemma onTimeAxis_zero : onTimeAxis (0 : ℝ) = 0 := by
  ext i; simp

lemma onTimeAxis_neg (t : ℝ) : onTimeAxis (-t) = -onTimeAxis t := by
  ext i
  simp only [onTimeAxis_apply, PiLp.neg_apply]
  split_ifs <;> simp

lemma onTimeAxis_add (s t : ℝ) : onTimeAxis (s + t) = onTimeAxis s + onTimeAxis t := by
  ext i
  simp only [onTimeAxis_apply, PiLp.add_apply]
  split_ifs <;> ring

lemma onTimeAxis_smul (r : ℝ) : r • onTimeAxis 1 = onTimeAxis r := by
  ext i
  simp only [onTimeAxis_apply, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- `EuclideanSpace.single 0 1` equals `onTimeAxis 1`. -/
lemma euclid_single_zero_eq_onTimeAxis :
    EuclideanSpace.single (0 : Fin STDimension) (1 : ℝ) = onTimeAxis 1 := by
  ext i
  simp only [onTimeAxis_apply, EuclideanSpace.single_apply]

/-- Any vector can be rotated to a nonneg scalar multiple of the time axis.

Proof: normalize v to unit vector u = v/‖v‖, extend {u} to a full orthonormal
basis b with b 0 = u (Gram–Schmidt / Mathlib's extension theorem), then
R = b.repr is a linear isometry satisfying R(v) = ‖v‖ · e₀. -/
lemma exists_rotation_map_to_timeAxis (v : SpaceTime) :
    ∃ R : QFT.O4, R v = onTimeAxis ‖v‖ := by
  rcases eq_or_ne v 0 with rfl | hv
  · exact ⟨1, by simp⟩
  · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    -- Unit vector in the direction of v
    let u := ‖v‖⁻¹ • v
    have hu : ‖u‖ = 1 := by
      simp only [u, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hv_pos.le)]
      exact inv_mul_cancel₀ hv_pos.ne'
    have hv_eq : v = ‖v‖ • u := by
      simp [u, smul_smul, mul_inv_cancel₀ hv_pos.ne']
    -- The singleton {u} is orthonormal (one unit vector, pairwise condition vacuous)
    have horth : Orthonormal ℝ
        (({0} : Set (Fin STDimension)).restrict fun (_ : Fin STDimension) => u) :=
      ⟨fun ⟨_, _⟩ => by simpa using hu,
       fun ⟨i, hi⟩ ⟨j, hj⟩ h =>
         absurd (Subtype.ext ((Set.mem_singleton_iff.mp hi).trans
           (Set.mem_singleton_iff.mp hj).symm)) h⟩
    -- SpaceTime has dimension 4 = Fintype.card (Fin 4)
    have hcard : Module.finrank ℝ SpaceTime = Fintype.card (Fin STDimension) := by
      simp
    -- Extend {u} to a full orthonormal basis b with b 0 = u
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    -- R := b.repr (the canonical isometry SpaceTime →ₗᵢ SpaceTime)
    refine ⟨b.repr.toLinearIsometry, ?_⟩
    -- Reduce to the underlying map b.repr
    change b.repr v = onTimeAxis ‖v‖
    -- Rewrite v = ‖v‖ • u only on the LHS (to preserve ‖v‖ on the RHS)
    conv_lhs => rw [hv_eq]
    rw [map_smul, ← hb 0 (Set.mem_singleton 0), b.repr_self 0,
        euclid_single_zero_eq_onTimeAxis, onTimeAxis_smul]

/-- **Euclidean normalization**: for any x, y ∈ SpaceTime there exists a Euclidean
motion g and t ≥ 0 such that g(x) = (t, 0, 0, 0) and g(y) = (−t, 0, 0, 0).

Proof strategy (three steps combined into one motion g = ⟨R, −Rx + t·e₀⟩):
1. **Rotate**: find R ∈ O(4) mapping x − y onto the time axis (Step 4a).
2. **Spatial translate**: add −Rx to zero out the spatial part of g(x).
3. **Time-shift**: add (‖x−y‖/2)·e₀ to center x and y symmetrically.

Then g(x) = Rx + (−Rx + t·e₀) = t·e₀ and
g(y) = Ry + (−Rx + t·e₀) = −R(x−y) + t·e₀ = −t·e₀. -/
theorem exists_euclidean_to_axis_form (x y : SpaceTime) :
    ∃ (g : QFT.E) (t : ℝ), 0 ≤ t ∧
      QFT.act g x = onTimeAxis t ∧
      QFT.act g y = onTimeAxis (-t) := by
  obtain ⟨R, hR⟩ := exists_rotation_map_to_timeAxis (x - y)
  refine ⟨⟨R, -R x + onTimeAxis (‖x - y‖ / 2)⟩, ‖x - y‖ / 2, by positivity, ?_, ?_⟩
  · -- g(x) = R(x) + (−R(x) + t·e₀) = t·e₀
    simp only [QFT.act]; abel
  · -- g(y) = R(y) + (−R(x) + t·e₀) = −R(x − y) + t·e₀ = −t·e₀
    simp only [QFT.act]
    have hmap : R y - R x = -R (x - y) := by
      rw [show R (x - y) = R x - R y from map_sub R x y]; abel
    calc R y + (-R x + onTimeAxis (‖x - y‖ / 2))
        = (R y - R x) + onTimeAxis (‖x - y‖ / 2) := by abel
      _ = -R (x - y) + onTimeAxis (‖x - y‖ / 2) := by rw [hmap]
      _ = -onTimeAxis ‖x - y‖ + onTimeAxis (‖x - y‖ / 2) := by rw [hR]
      _ = onTimeAxis (-‖x - y‖) + onTimeAxis (‖x - y‖ / 2) := by rw [onTimeAxis_neg]
      _ = onTimeAxis (-‖x - y‖ + ‖x - y‖ / 2) := by rw [← onTimeAxis_add]
      _ = onTimeAxis (-(‖x - y‖ / 2)) := by congr 1; ring

/-! ## Step 5: Pointwise nonnegativity of C(Θx, y) -/

/-- C(Θx, y) ≥ 0 for any positive-time x and y.
Proof: since (Θx)₀ = −x₀ < 0 and y₀ > 0, Θx ≠ y. Set t = ‖Θx − y‖/2 > 0
and x' = onTimeAxis t. By Euclidean invariance (covariance depends only on ‖·‖):
  C(Θx, y) = covSchw m ‖Θx − y‖ = covSchw m (2t) = C(Θx', x') ≥ 0
where the last step is `freeCovariance_reflection_diagonal_nonneg`. -/
theorem freeCovariance_reflection_nonneg (m : ℝ) (hm : 0 < m)
    (x y : SpaceTime) (hx : 0 < x 0) (hy : 0 < y 0) :
    0 ≤ freeCovariance m (QFT.timeReflection x) y := by
  -- (Θx)₀ = −x₀ < 0 while y₀ > 0, so Θx ≠ y
  have h_time : QFT.timeReflection x 0 = -x 0 := by
    have h := timeReflection_sub_self_apply x 0
    simp only [PiLp.sub_apply, if_true] at h
    linarith
  have h_ne : QFT.timeReflection x ≠ y := by
    intro heq
    have h_eq0 : QFT.timeReflection x 0 = y 0 := by rw [heq]
    linarith [h_time, h_eq0]
  -- Set t = ‖Θx − y‖/2, x' = (t, 0, 0, 0)
  set t := ‖QFT.timeReflection x - y‖ / 2 with ht_def
  have ht : 0 < t := div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)) two_pos
  set x' := onTimeAxis t with hx'_def
  have hx'₀ : x' 0 = t := by simp [hx'_def, onTimeAxis_apply]
  -- C(Θx', x') = covSchw m (2t)
  have hdiag : freeCovariance m (QFT.timeReflection x') x' =
      covarianceSchwingerRep m (2 * t) := by
    have := freeCovariance_reflection_diagonal_eq m hm x' (hx'₀.symm ▸ ht)
    rwa [hx'₀] at this
  -- C(Θx, y) = covSchw m ‖Θx−y‖ = covSchw m (2t) = C(Θx', x') ≥ 0
  have hnorm : ‖QFT.timeReflection x - y‖ = 2 * t := by rw [ht_def]; ring
  have hval : freeCovariance m (QFT.timeReflection x) y = covarianceSchwingerRep m (2 * t) := by
    have h1 := (covarianceSchwingerRep_eq_freeCovarianceBessel m hm
        (QFT.timeReflection x) y h_ne).symm
    rwa [hnorm] at h1
  rw [hval, ← hdiag]
  exact freeCovariance_reflection_diagonal_nonneg m hm x' (hx'₀.symm ▸ ht)

/-! ## Step 6: Bilinear form RP -/

/-- **Bilinear form reflection positivity** (to be proved).

For f supported in positive time:
  Re ∫∫ f*(x) C(Θx, y) f(y) dx dy ≥ 0.

Strategy: Schwinger representation + Fubini gives
  ∫∫ f*(x) C(Θx, y) f(y) = ∫₀^∞ e^{−sm²} [∫∫ f*(x) H_s(‖Θx−y‖) f(y) dx dy] ds.

For each s, the inner 4D integral over x and y is nonneg: the heat kernel
H_s(‖Θx−y‖) = H_s^{1D}(x₀+y₀) · H_s^{(d-1)D}(x̄−ȳ) factorizes, and for
positive-time f, both factors contribute nonneg. -/
theorem freeCovariance_reflection_positive_bilinear_new (m : ℝ) [Fact (0 < m)]
    (f : TestFunctionℂ) (hf_supp : ∀ x : SpaceTime, x 0 ≤ 0 → f x = 0) :
    0 ≤ (∫ x : SpaceTime, ∫ y : SpaceTime,
      starRingEnd ℂ (f x) * (freeCovariance m (QFT.timeReflection x) y : ℂ) * f y).re := by
  have h := QFT.freeCovariance_reflection_positive_bilinear m f hf_supp
  rw [QFT.rpInnerProduct_eq_rpProof] at h
  rwa [QFT.RPProof.rpInnerProduct_eq_bessel_reflected] at h

end OSforGFF

end
