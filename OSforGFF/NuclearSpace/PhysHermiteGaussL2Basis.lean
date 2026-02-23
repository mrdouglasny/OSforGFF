/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Exponential
import OSforGFF.NuclearSpace.PhysHermite

/-!
# Completeness of physicists' Hermite polynomials in Gaussian-weight `L²(ℝ)`

This file formalizes the analytic core of the 1D Hermite completeness argument needed for the
Hermite-expansion approach to Schwartz nuclearity.

Main result (in this file):

* If `g ∈ L²(ℝ, e^{-x²} dx)` is orthogonal to every `physHermite n`, then `g = 0` a.e. for the
  Gaussian-weight measure.

The proof follows the characteristic-function strategy (`Measure.ext_of_charFun`) combined with
dominated convergence, with explicit exponential bounds for the cosine/sine power series partial
sums.
-/

open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace Nat

namespace PhysLean

noncomputable section

open MeasureTheory

namespace PhysHermiteGauss

/-! ## The Gaussian-weight measure `e^{-x²} dx` -/

/-- The (finite) measure `e^{-x²} dx` on `ℝ`. -/
noncomputable def gaussMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (Real.exp (-x ^ 2)))

lemma gaussMeasure_def :
    gaussMeasure = (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (Real.exp (-x ^ 2))) :=
  rfl

instance instIsFiniteMeasure_gaussMeasure : IsFiniteMeasure gaussMeasure := by
  -- `∫ e^{-x²} < ∞` hence `withDensity` is finite.
  have hInt : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) (volume : Measure ℝ) := by
    simpa [one_mul] using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by positivity))
  have hLin :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) ∂(volume : Measure ℝ)) ≠ ∞ := by
    have hmeas :
        AEStronglyMeasurable (fun x : ℝ => Real.exp (-x ^ 2)) (volume : Measure ℝ) := by
      fun_prop
    have hnonneg : 0 ≤ᵐ[volume] (fun x : ℝ => Real.exp (-x ^ 2)) := by
      exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := (volume : Measure ℝ))
            (f := fun x : ℝ => Real.exp (-x ^ 2)) hmeas hnonneg).2 hInt
  simpa [gaussMeasure_def] using
    (MeasureTheory.isFiniteMeasure_withDensity (μ := (volume : Measure ℝ)) hLin)

/-! ## Power-series partial sums and uniform bounds -/

private def cosPartial (t : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * (t * x) ^ (2 * n) / ((2 * n)! : ℝ)

private def sinPartial (t : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1) ^ n * (t * x) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)

private lemma abs_cosPartial_le_exp (t x : ℝ) (N : ℕ) :
    |cosPartial t N x| ≤ Real.exp (|t| * |x|) := by
  classical
  have htx : 0 ≤ |t| * |x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- First bound by the sum of absolute values.
  have h1 :
      |cosPartial t N x| ≤
        ∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n) / ((2 * n)! : ℝ) := by
    -- `abs_sum_le_sum_abs` then simplify.
    have :=
      (Finset.abs_sum_le_sum_abs
        (f := fun n : ℕ => (-1) ^ n * (t * x) ^ (2 * n) / ((2 * n)! : ℝ))
        (s := Finset.range N))
    -- unfold and simplify
    simpa [cosPartial, abs_mul, abs_div, abs_pow, abs_mul, mul_pow, abs_of_nonneg htx] using this
  -- Now compare the even-term sum to the full exponential sum.
  have h2 :
      (∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n) / ((2 * n)! : ℝ)) ≤
        ∑ k ∈ Finset.range (2 * N), (|t| * |x|) ^ k / (k ! : ℕ) := by
    -- reindex the LHS as a sum over even indices, then use monotonicity of finite sums
    let E : Finset ℕ := (Finset.range N).image (fun n => 2 * n)
    have hEsub : E ⊆ Finset.range (2 * N) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
      exact Finset.mem_range.mpr (by
        have : n < N := Finset.mem_range.mp hn
        nlinarith)
    have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
      intro a b hab
      exact Nat.mul_left_cancel zero_lt_two (by simpa using hab)
    -- rewrite LHS
    have hL :
        (∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n) / ((2 * n)! : ℝ)) =
          ∑ k ∈ E, (|t| * |x|) ^ k / (k ! : ℕ) := by
      -- `sum_image` for an injective map
      simpa [E, hinj, Finset.sum_image, Nat.cast_mul]  -- the casts are on factorials
    -- apply subset bound
    rw [hL]
    refine Finset.sum_le_sum_of_subset_of_nonneg hEsub ?_
    intro k hk hknot
    positivity
  -- Finish with `Real.sum_le_exp_of_nonneg`.
  have h3 :
      (∑ k ∈ Finset.range (2 * N), (|t| * |x|) ^ k / (k ! : ℕ)) ≤ Real.exp (|t| * |x|) :=
    Real.sum_le_exp_of_nonneg htx (2 * N)
  exact h1.trans (h2.trans h3)

private lemma abs_sinPartial_le_exp (t x : ℝ) (N : ℕ) :
    |sinPartial t N x| ≤ Real.exp (|t| * |x|) := by
  classical
  have htx : 0 ≤ |t| * |x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 :
      |sinPartial t N x| ≤
        ∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) := by
    have :=
      (Finset.abs_sum_le_sum_abs
        (f := fun n : ℕ => (-1) ^ n * (t * x) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ))
        (s := Finset.range N))
    simpa [sinPartial, abs_mul, abs_div, abs_pow, abs_mul, mul_pow, abs_of_nonneg htx] using this
  have h2 :
      (∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)) ≤
        ∑ k ∈ Finset.range (2 * N + 1), (|t| * |x|) ^ k / (k ! : ℕ) := by
    let O : Finset ℕ := (Finset.range N).image (fun n => 2 * n + 1)
    have hOsub : O ⊆ Finset.range (2 * N + 1) := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
      exact Finset.mem_range.mpr (by
        have : n < N := Finset.mem_range.mp hn
        nlinarith)
    have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
      intro a b hab
      have h' : 2 * a = 2 * b := by
        exact Nat.add_right_cancel hab
      exact Nat.mul_left_cancel zero_lt_two h'
    have hL :
        (∑ n ∈ Finset.range N, (|t| * |x|) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)) =
          ∑ k ∈ O, (|t| * |x|) ^ k / (k ! : ℕ) := by
      simpa [O, hinj, Finset.sum_image, Nat.cast_add, Nat.cast_mul]  -- casts for factorials
    rw [hL]
    refine Finset.sum_le_sum_of_subset_of_nonneg hOsub ?_
    intro k hk hknot
    positivity
  have h3 :
      (∑ k ∈ Finset.range (2 * N + 1), (|t| * |x|) ^ k / (k ! : ℕ)) ≤ Real.exp (|t| * |x|) :=
    Real.sum_le_exp_of_nonneg htx (2 * N + 1)
  exact h1.trans (h2.trans h3)

/-! ## `L²`-integrability of the exponential weight needed for dominated convergence -/

private lemma memLp_exp_abs_mul_abs (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (|t| * |x|)) 2 gaussMeasure := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => Real.exp (|t| * |x|)) gaussMeasure := by
    fun_prop
  refine (MeasureTheory.memLp_two_iff_integrable_sq (μ := gaussMeasure)
    (f := fun x : ℝ => Real.exp (|t| * |x|)) hmeas).2 ?_
  -- Reduce to an integrability statement on `volume` using `integrable_withDensity_iff`.
  have hflt :
      ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (ENNReal.ofReal (Real.exp (-x ^ 2))) < ∞ := by
    exact ae_of_all _ (fun _ => by simp)
  have hwd :
      Integrable (fun x : ℝ => (Real.exp (|t| * |x|)) ^ 2) gaussMeasure ↔
        Integrable
          (fun x : ℝ =>
            (Real.exp (|t| * |x|)) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal)
          (volume : Measure ℝ) := by
    simpa [gaussMeasure_def, gaussMeasure] using
      (integrable_withDensity_iff (μ := (volume : Measure ℝ))
        (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)))
        (hf := by fun_prop) hflt (g := fun x : ℝ => (Real.exp (|t| * |x|)) ^ 2))
  -- It suffices to prove the RHS integrable; we bound it by a Gaussian.
  refine (hwd.mpr ?_)
  have hpos : ∀ x : ℝ, 0 ≤ Real.exp (-x ^ 2) := fun _ => (Real.exp_pos _).le
  -- simplify the density factor
  have hsimp :
      (fun x : ℝ =>
        (Real.exp (|t| * |x|)) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal) =
        fun x : ℝ => Real.exp (2 * |t| * |x|) * Real.exp (-x ^ 2) := by
    funext x
    have hxnonneg : 0 ≤ Real.exp (-x ^ 2) := hpos x
    -- rewrite `(exp a)^2` as `exp (2a)`
    have hsq : (Real.exp (|t| * |x|)) ^ 2 = Real.exp (2 * |t| * |x|) := by
      calc
        (Real.exp (|t| * |x|)) ^ 2
            = Real.exp (|t| * |x|) * Real.exp (|t| * |x|) := by simp [pow_two]
        _ = Real.exp ((|t| * |x|) + (|t| * |x|)) := by
              simpa [Real.exp_add] using (Real.exp_add (|t| * |x|) (|t| * |x|)).symm
        _ = Real.exp (2 * |t| * |x|) := by
              congr 1
              ring
    -- finish (avoid `simp` rewriting `x ^ 2` into `x * x`)
    calc
      (Real.exp (|t| * |x|)) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal
          = (Real.exp (|t| * |x|)) ^ 2 * Real.exp (-x ^ 2) := by
                simp [ENNReal.toReal_ofReal hxnonneg]
      _ = Real.exp (2 * |t| * |x|) * Real.exp (-x ^ 2) := by
            simp [hsq, mul_assoc]
  -- use comparison `exp(2|t||x|) * exp(-x²) ≤ exp(2|t|²) * exp(-(1/2)x²)`
  have hle :
      (fun x : ℝ => Real.exp (2 * |t| * |x|) * Real.exp (-x ^ 2)) ≤ᵐ[volume]
        fun x : ℝ => Real.exp (2 * |t| ^ 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    refine ae_of_all _ (fun x => ?_)
    have hx :
        (-x ^ 2 : ℝ) + 2 * |t| * |x| ≤ (-(1 / 2 : ℝ) * x ^ 2) + 2 * |t| ^ 2 := by
      have hmul : 2 * |t| * |x| ≤ (1 / 2 : ℝ) * x ^ 2 + 2 * |t| ^ 2 := by
        -- start from `2 * |x| * (2*|t|) ≤ |x|^2 + (2*|t|)^2` and divide by 2
        have h0 : |t| * (|x| * (2 * 2)) ≤ x * x + |t| * (|t| * (2 * 2)) := by
          -- `two_mul_le_add_sq (|x|) (2*|t|)` with squares expanded
          simpa [pow_two, sq_abs x, mul_assoc, mul_left_comm, mul_comm] using
            (two_mul_le_add_sq (|x|) (2 * |t|))
        nlinarith [h0]
      nlinarith [hmul]
    have := Real.exp_le_exp.mpr hx
    -- rewrite products as `exp` of sums
    simpa [Real.exp_add, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm, mul_comm] using this
  have hInt :
      Integrable (fun x : ℝ => Real.exp (2 * t ^ 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (volume : Measure ℝ) := by
    simpa [mul_assoc] using
      ((integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by positivity)).const_mul (Real.exp (2 * t ^ 2)))
  -- conclude by monotone comparison
  have hle' :
      (fun x : ℝ => Real.exp (2 * |t| * |x|) * Real.exp (-x ^ 2)) ≤ᵐ[volume]
        fun x : ℝ => Real.exp (2 * t ^ 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    simpa [sq_abs t] using hle
  simpa [hsimp] using hInt.mono' (by fun_prop) (by simpa [hsimp] using hle')

private lemma integrable_abs_mul_exp_abs_mul (t : ℝ) {g : ℝ → ℝ} (hg : MemLp g 2 gaussMeasure) :
    Integrable (fun x : ℝ => |g x| * Real.exp (|t| * |x|)) gaussMeasure := by
  have hg_abs : MemLp (fun x : ℝ => |g x|) 2 gaussMeasure := by
    simpa [Real.norm_eq_abs] using hg.norm
  have h_exp : MemLp (fun x : ℝ => Real.exp (|t| * |x|)) 2 gaussMeasure :=
    memLp_exp_abs_mul_abs t
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (MeasureTheory.MemLp.integrable_mul (μ := gaussMeasure) hg_abs h_exp)

/-! ## Span membership for the partial sums -/

private lemma cosPartial_mem_span (t : ℝ) (N : ℕ) :
    (fun x : ℝ => cosPartial t N x) ∈
      Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) := by
  -- copy the polynomial argument from `cos_mem_physHermite_span_topologicalClosure`
  classical
  have h0 :
      (fun x : ℝ => cosPartial t N x) =
        ∑ n ∈ Finset.range N,
          (((-1) ^ n * t ^ (2 * n) / ((2 * n)! : ℝ)) • fun (x : ℝ) => x ^ (2 * n)) := by
    funext x
    simp [cosPartial, mul_pow, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul]
    congr
    funext n
    ring
  rw [h0]
  refine Submodule.sum_mem (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))) ?_
  intro n hn
  -- show the monomial belongs to the span
  refine Submodule.smul_mem _ _ ?_
  let P : Polynomial ℤ := (Polynomial.X : Polynomial ℤ) ^ (2 * n)
  have hmon : (fun x : ℝ => x ^ (2 * n)) = fun x : ℝ => P.aeval x := by
    funext x
    simp [P]
  exact hmon ▸ polynomial_mem_physHermite_span P

private lemma sinPartial_mem_span (t : ℝ) (N : ℕ) :
    (fun x : ℝ => sinPartial t N x) ∈
      Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) := by
  classical
  have h0 :
      (fun x : ℝ => sinPartial t N x) =
        ∑ n ∈ Finset.range N,
          (((-1) ^ n * t ^ (2 * n + 1) / ((2 * n + 1)! : ℝ)) • fun (x : ℝ) => x ^ (2 * n + 1)) := by
    funext x
    simp [sinPartial, mul_pow, mul_assoc, mul_left_comm, mul_comm, smul_eq_mul]
    congr
    funext n
    ring
  rw [h0]
  refine Submodule.sum_mem (Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))) ?_
  intro n hn
  refine Submodule.smul_mem _ _ ?_
  let P : Polynomial ℤ := (Polynomial.X : Polynomial ℤ) ^ (2 * n + 1)
  have hmon : (fun x : ℝ => x ^ (2 * n + 1)) = fun x : ℝ => P.aeval x := by
    funext x
    simp [P]
  exact hmon ▸ polynomial_mem_physHermite_span P

/-! ## Orthogonality to all `physHermite` implies zero -/

private lemma integral_mul_eq_zero_of_mem_span
    {g : ℝ → ℝ} (hg : MemLp g 2 gaussMeasure)
    (horth : ∀ n : ℕ, ∫ x : ℝ, g x * (physHermite n x) ∂gaussMeasure = 0)
    {phi : ℝ → ℝ}
    (hphi : phi ∈ Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ)))) :
    ∫ x : ℝ, g x * phi x ∂gaussMeasure = 0 := by
  -- prove the stronger statement by span induction
  classical
  -- predicate closed under span operations
  let P : (ℝ → ℝ) → Prop :=
    fun phi => Integrable (fun x : ℝ => g x * phi x) gaussMeasure ∧
      (∫ x : ℝ, g x * phi x ∂gaussMeasure = 0)
  have hP_gen : ∀ n : ℕ, P (physHermite n) := by
    intro n
    -- integrability from `L² × L² → L¹`
    -- `physHermite n` has Gaussian moments, so it lies in `L²` for `gaussMeasure`
    have hphysL2 : MemLp (fun x : ℝ => (physHermite n x : ℝ)) 2 gaussMeasure := by
      -- use `guassian_integrable_polynomial_cons` on the polynomial `(physHermite n)^2`
      have hmeas : AEStronglyMeasurable (fun x : ℝ => (physHermite n x : ℝ)) gaussMeasure := by
        fun_prop
      refine (MeasureTheory.memLp_two_iff_integrable_sq (μ := gaussMeasure)
        (f := fun x : ℝ => (physHermite n x : ℝ)) hmeas).2 ?_
      -- reduce to integrability on `volume`
      have hflt :
          ∀ᵐ x : ℝ ∂(volume : Measure ℝ), (ENNReal.ofReal (Real.exp (-x ^ 2))) < ∞ := by
        exact ae_of_all _ (fun _ => by simp)
      have hwd :
          Integrable (fun x : ℝ => (physHermite n x : ℝ) ^ 2) gaussMeasure ↔
            Integrable
              (fun x : ℝ =>
                (physHermite n x : ℝ) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal)
              (volume : Measure ℝ) := by
        simpa [gaussMeasure_def, gaussMeasure] using
          (integrable_withDensity_iff (μ := (volume : Measure ℝ))
            (f := fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)))
            (hf := by fun_prop) hflt (g := fun x : ℝ => (physHermite n x : ℝ) ^ 2))
      -- integrable RHS: polynomial times Gaussian
      have hRHS :
          Integrable
            (fun x : ℝ =>
              ((physHermite n : Polynomial ℤ) * physHermite n).aeval x * Real.exp (-x ^ 2))
            (volume : Measure ℝ) := by
        -- `guassian_integrable_polynomial_cons` with `b = 1`, `c = 1`.
        simpa [mul_assoc, one_mul] using
          (guassian_integrable_polynomial_cons (b := (1 : ℝ)) (c := (1 : ℝ))
            (hb := by positivity) ((physHermite n) * physHermite n))
      have hpos : ∀ x : ℝ, 0 ≤ Real.exp (-x ^ 2) := fun _ => (Real.exp_pos _).le
      have hsimp :
          (fun x : ℝ =>
            (physHermite n x : ℝ) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal) =
            fun x : ℝ => ((physHermite n x) * (physHermite n x)) * Real.exp (-x ^ 2) := by
        funext x
        have hxnonneg : 0 ≤ Real.exp (-x ^ 2) := hpos x
        calc
          (physHermite n x : ℝ) ^ 2 * (ENNReal.ofReal (Real.exp (-x ^ 2))).toReal
              = (physHermite n x : ℝ) ^ 2 * Real.exp (-x ^ 2) := by
                    simp [ENNReal.toReal_ofReal hxnonneg]
          _ = ((physHermite n x) * (physHermite n x)) * Real.exp (-x ^ 2) := by
                simp [pow_two, mul_assoc]
      have : Integrable (fun x : ℝ => ((physHermite n x) * (physHermite n x)) * Real.exp (-x ^ 2))
          (volume : Measure ℝ) := by
        -- rewrite `hRHS`
        simpa [Polynomial.aeval_mul, mul_assoc, mul_left_comm, mul_comm] using hRHS
      -- transfer back
      refine (hwd.mpr ?_)
      simpa [hsimp] using this
    have hInt : Integrable (fun x : ℝ => g x * (physHermite n x)) gaussMeasure :=
      (MeasureTheory.MemLp.integrable_mul (μ := gaussMeasure) hg hphysL2)
    exact ⟨hInt, by simpa using (horth n)⟩
  have hP_zero : P 0 := by
    simp [P]
  have hP_add : ∀ {f g'}, P f → P g' → P (f + g') := by
    intro f g' hf hg'
    refine ⟨?_, ?_⟩
    · simpa [mul_add, add_mul] using hf.1.add hg'.1
    ·
      simpa [mul_add, add_mul, integral_add hf.1 hg'.1, hf.2, hg'.2]
  have hP_smul : ∀ (a : ℝ) {f}, P f → P (a • f) := by
    intro a f hf
    refine ⟨?_, ?_⟩
    · simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        (hf.1.mul_const a)
    · simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
        (MeasureTheory.integral_const_mul a (fun x : ℝ => g x * f x)).trans (by simpa [hf.2])
  -- apply `span_induction`
  have : P phi := by
    refine Submodule.span_induction (p := fun x _hx => P x)
      (s := Set.range (fun n => (physHermite n : ℝ → ℝ))) ?_ hP_zero ?_ ?_ hphi
    · rintro _ ⟨n, rfl⟩
      simpa using hP_gen n
    · intro f g' hf hg' hfP hgP
      exact hP_add hfP hgP
    · intro a f hf hfP
      exact hP_smul a hfP
  exact this.2

theorem ae_eq_zero_of_forall_integral_physHermite_eq_zero
    {g : ℝ → ℝ} (hg : MemLp g 2 gaussMeasure)
    (horth : ∀ n : ℕ, ∫ x : ℝ, g x * (physHermite n x) ∂gaussMeasure = 0) :
    g =ᵐ[gaussMeasure] 0 := by
  classical
  -- Positive and negative density measures with respect to `gaussMeasure`.
  let ρpos : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (g x) 0)
  let ρneg : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (max (-g x) 0)
  let μpos : Measure ℝ := gaussMeasure.withDensity ρpos
  let μneg : Measure ℝ := gaussMeasure.withDensity ρneg

  -- `μpos` and `μneg` are finite measures since `g ∈ L²` and `gaussMeasure` is finite.
  have hg1 : Integrable g gaussMeasure := by
    have : MemLp g 1 gaussMeasure :=
      hg.mono_exponent (μ := gaussMeasure) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
    exact memLp_one_iff_integrable.mp this
  have hposInt : Integrable (fun x : ℝ => max (g x) 0) gaussMeasure := hg1.pos_part
  have hnegInt : Integrable (fun x : ℝ => max (-g x) 0) gaussMeasure := hg1.neg_part
  have hLinPos : (∫⁻ x : ℝ, ρpos x ∂gaussMeasure) ≠ ∞ := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => max (g x) 0) gaussMeasure := hposInt.1
    have hnonneg : 0 ≤ᵐ[gaussMeasure] (fun x : ℝ => max (g x) 0) :=
      ae_of_all _ (fun _ => le_max_right _ _)
    simpa [ρpos] using
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := gaussMeasure)
        (f := fun x : ℝ => max (g x) 0) hmeas hnonneg).2 hposInt
  have hLinNeg : (∫⁻ x : ℝ, ρneg x ∂gaussMeasure) ≠ ∞ := by
    have hmeas : AEStronglyMeasurable (fun x : ℝ => max (-g x) 0) gaussMeasure := hnegInt.1
    have hnonneg : 0 ≤ᵐ[gaussMeasure] (fun x : ℝ => max (-g x) 0) :=
      ae_of_all _ (fun _ => le_max_right _ _)
    simpa [ρneg] using
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable (μ := gaussMeasure)
        (f := fun x : ℝ => max (-g x) 0) hmeas hnonneg).2 hnegInt
  haveI : IsFiniteMeasure μpos := MeasureTheory.isFiniteMeasure_withDensity (μ := gaussMeasure) hLinPos
  haveI : IsFiniteMeasure μneg := MeasureTheory.isFiniteMeasure_withDensity (μ := gaussMeasure) hLinNeg

  -- Show `charFun μpos = charFun μneg` by proving the Fourier integral against `g` vanishes.
  have hcos0 (t : ℝ) : ∫ x : ℝ, g x * Real.cos (t * x) ∂gaussMeasure = 0 := by
    -- Dominated convergence from the cosine series.
    have hT :
        Filter.Tendsto
          (fun N : ℕ => ∫ x : ℝ, g x * cosPartial t N x ∂gaussMeasure)
          Filter.atTop
          (nhds (∫ x : ℝ, g x * Real.cos (t * x) ∂gaussMeasure)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := gaussMeasure)
        (F := fun N x => g x * cosPartial t N x)
        (f := fun x => g x * Real.cos (t * x))
        (bound := fun x => |g x| * Real.exp (|t| * |x|)) ?_ ?_ ?_ ?_
      ·
        refine Filter.Eventually.of_forall (fun N => ?_)
        have hg_meas : AEStronglyMeasurable g gaussMeasure := hg.aestronglyMeasurable
        have hcos_meas : AEStronglyMeasurable (fun x : ℝ => cosPartial t N x) gaussMeasure := by
          classical
          simpa [cosPartial] using (by
            fun_prop :
              AEStronglyMeasurable
                (fun x : ℝ =>
                  ∑ n ∈ Finset.range N, (-1) ^ n * (t * x) ^ (2 * n) / ((2 * n)! : ℝ))
                gaussMeasure)
        simpa [mul_assoc] using hg_meas.mul hcos_meas
      ·
        exact Filter.Eventually.of_forall (fun N => by
          refine ae_of_all _ (fun x => ?_)
          have hb := abs_cosPartial_le_exp t x N
          have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg (g x))
          simpa [Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul)
      · simpa using integrable_abs_mul_exp_abs_mul t (g := g) hg
      · refine ae_of_all _ (fun x => ?_)
        have hlim :
            Filter.Tendsto (fun N : ℕ => cosPartial t N x) Filter.atTop
              (nhds (Real.cos (t * x))) := by
          -- `HasSum` → convergence of range partial sums
          simpa [cosPartial, HasSum] using (Real.hasSum_cos (t * x)).tendsto_sum_nat
        simpa [mul_assoc] using (Filter.Tendsto.const_mul (g x) hlim)
    have hzero : ∀ N : ℕ, (∫ x : ℝ, g x * cosPartial t N x ∂gaussMeasure) = 0 := by
      intro N
      have hmem : (fun x : ℝ => cosPartial t N x) ∈
          Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) :=
        cosPartial_mem_span t N
      simpa [cosPartial] using (integral_mul_eq_zero_of_mem_span (g := g) hg horth hmem)
    -- take limits
    have hT0 :
        Filter.Tendsto
          (fun N : ℕ => ∫ x : ℝ, g x * cosPartial t N x ∂gaussMeasure)
          Filter.atTop
          (nhds (0 : ℝ)) := by
      refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)).congr' ?_
      exact Filter.Eventually.of_forall (fun N => (hzero N).symm)
    have hlim := tendsto_nhds_unique hT hT0
    simpa using hlim

  have hsin0 (t : ℝ) : ∫ x : ℝ, g x * Real.sin (t * x) ∂gaussMeasure = 0 := by
    have hT :
        Filter.Tendsto
          (fun N : ℕ => ∫ x : ℝ, g x * sinPartial t N x ∂gaussMeasure)
          Filter.atTop
          (nhds (∫ x : ℝ, g x * Real.sin (t * x) ∂gaussMeasure)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := gaussMeasure)
        (F := fun N x => g x * sinPartial t N x)
        (f := fun x => g x * Real.sin (t * x))
        (bound := fun x => |g x| * Real.exp (|t| * |x|)) ?_ ?_ ?_ ?_
      ·
        refine Filter.Eventually.of_forall (fun N => ?_)
        have hg_meas : AEStronglyMeasurable g gaussMeasure := hg.aestronglyMeasurable
        have hsin_meas : AEStronglyMeasurable (fun x : ℝ => sinPartial t N x) gaussMeasure := by
          classical
          simpa [sinPartial] using (by
            fun_prop :
              AEStronglyMeasurable
                (fun x : ℝ =>
                  ∑ n ∈ Finset.range N, (-1) ^ n * (t * x) ^ (2 * n + 1) / ((2 * n + 1)! : ℝ))
                gaussMeasure)
        simpa [mul_assoc] using hg_meas.mul hsin_meas
      ·
        exact Filter.Eventually.of_forall (fun N => by
          refine ae_of_all _ (fun x => ?_)
          have hb := abs_sinPartial_le_exp t x N
          have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg (g x))
          simpa [Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul)
      · simpa using integrable_abs_mul_exp_abs_mul t (g := g) hg
      · refine ae_of_all _ (fun x => ?_)
        have hlim :
            Filter.Tendsto (fun N : ℕ => sinPartial t N x) Filter.atTop
              (nhds (Real.sin (t * x))) := by
          simpa [sinPartial, HasSum] using (Real.hasSum_sin (t * x)).tendsto_sum_nat
        simpa [mul_assoc] using (Filter.Tendsto.const_mul (g x) hlim)
    have hzero : ∀ N : ℕ, (∫ x : ℝ, g x * sinPartial t N x ∂gaussMeasure) = 0 := by
      intro N
      have hmem : (fun x : ℝ => sinPartial t N x) ∈
          Submodule.span ℝ (Set.range (fun n => (physHermite n : ℝ → ℝ))) :=
        sinPartial_mem_span t N
      simpa [sinPartial] using (integral_mul_eq_zero_of_mem_span (g := g) hg horth hmem)
    have hT0 :
        Filter.Tendsto
          (fun N : ℕ => ∫ x : ℝ, g x * sinPartial t N x ∂gaussMeasure)
          Filter.atTop
          (nhds (0 : ℝ)) := by
      refine (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)).congr' ?_
      exact Filter.Eventually.of_forall (fun N => (hzero N).symm)
    have hlim := tendsto_nhds_unique hT hT0
    simpa using hlim

  have hchar : ∀ t : ℝ, MeasureTheory.charFun μpos t = MeasureTheory.charFun μneg t := by
    intro t
    -- rewrite `charFun` using `withDensity`
    have hflt_pos : ∀ᵐ x : ℝ ∂gaussMeasure, ρpos x < ∞ := ae_of_all _ (fun _ => by simp [ρpos])
    have hflt_neg : ∀ᵐ x : ℝ ∂gaussMeasure, ρneg x < ∞ := ae_of_all _ (fun _ => by simp [ρneg])
    have hρpos_meas : AEMeasurable ρpos gaussMeasure := by
      have : AEMeasurable (fun x : ℝ => max (g x) 0) gaussMeasure := hposInt.1.aemeasurable
      simpa [ρpos] using this.ennreal_ofReal
    have hρneg_meas : AEMeasurable ρneg gaussMeasure := by
      have : AEMeasurable (fun x : ℝ => max (-g x) 0) gaussMeasure := hnegInt.1.aemeasurable
      simpa [ρneg] using this.ennreal_ofReal
    -- compute both integrals on the base measure
    have hpos :
        MeasureTheory.charFun μpos t =
          ∫ x : ℝ, ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
      -- use the `AEMeasurable` version to avoid global measurability assumptions on `g`
      have hwd :
          (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂gaussMeasure.withDensity ρpos) =
            ∫ x : ℝ, ((ρpos x).toReal : ℝ) • Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
        simpa using
          (integral_withDensity_eq_integral_toReal_smul₀ (μ := gaussMeasure) (f := ρpos)
            hρpos_meas hflt_pos (g := fun x : ℝ => Complex.exp (t * x * Complex.I)))
      -- convert `•` into multiplication in `ℂ`
      have hsmul :
          (fun x : ℝ => ((ρpos x).toReal : ℝ) • Complex.exp (t * x * Complex.I)) =
            fun x : ℝ => ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) := by
        funext x
        simp [Algebra.smul_def]
      -- assemble
      simp [MeasureTheory.charFun_apply_real, μpos, hwd, hsmul]
    have hneg :
        MeasureTheory.charFun μneg t =
          ∫ x : ℝ, ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
      have hwd :
          (∫ x : ℝ, Complex.exp (t * x * Complex.I) ∂gaussMeasure.withDensity ρneg) =
            ∫ x : ℝ, ((ρneg x).toReal : ℝ) • Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
        simpa using
          (integral_withDensity_eq_integral_toReal_smul₀ (μ := gaussMeasure) (f := ρneg)
            hρneg_meas hflt_neg (g := fun x : ℝ => Complex.exp (t * x * Complex.I)))
      have hsmul :
          (fun x : ℝ => ((ρneg x).toReal : ℝ) • Complex.exp (t * x * Complex.I)) =
            fun x : ℝ => ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) := by
        funext x
        simp [Algebra.smul_def]
      simp [MeasureTheory.charFun_apply_real, μneg, hwd, hsmul]
    -- difference equals the Fourier integral against `g`
    have hdiff :
        (fun x : ℝ => ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I)) -
          (fun x : ℝ => ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I)) =
          fun x : ℝ => (g x : ℂ) * Complex.exp (t * x * Complex.I) := by
      funext x
      have : (ρpos x).toReal - (ρneg x).toReal = g x := by
        -- expand the `toReal` of the `ofReal (max _ 0)` densities, then use `max - max(-) = id`
        dsimp [ρpos, ρneg]
        -- `toReal (ofReal a) = a` when `a ≥ 0`, and `max _ 0` is nonnegative
        rw [ENNReal.toReal_ofReal (le_max_right (g x) 0)]
        rw [ENNReal.toReal_ofReal (le_max_right (-g x) 0)]
        simpa using (max_zero_sub_max_neg_zero_eq_self (g x))
      -- factor out the common exponential term
      have hcast : ((ρpos x).toReal : ℂ) - ((ρneg x).toReal : ℂ) = (g x : ℂ) := by
        -- cast the real identity into `ℂ`
        have := congrArg (fun r : ℝ => (r : ℂ)) this
        -- rewrite `((a - b : ℝ) : ℂ)` as `(a : ℂ) - (b : ℂ)`
        simpa [Complex.ofReal_sub] using this
      -- finish by factoring and rewriting
      calc
        ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) -
            ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I)
            = (((ρpos x).toReal : ℂ) - ((ρneg x).toReal : ℂ)) * Complex.exp (t * x * Complex.I) := by
                simpa using
                  (sub_mul ((ρpos x).toReal : ℂ) ((ρneg x).toReal : ℂ) (Complex.exp (t * x * Complex.I))).symm
        _ = (g x : ℂ) * Complex.exp (t * x * Complex.I) := by simpa [hcast]
    -- show the RHS integral is 0 using `hcos0` and `hsin0`
    have hexp0 :
        ∫ x : ℝ, (g x : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure = 0 := by
      -- expand `exp(a*I) = cos a + sin a * I`
      have hrepr :
          (fun x : ℝ => (g x : ℂ) * Complex.exp (t * x * Complex.I)) =
            fun x : ℝ =>
              (g x * Real.cos (t * x) : ℂ) + (g x * Real.sin (t * x) : ℂ) * Complex.I := by
        funext x
        -- rewrite `exp((t*x)*I)` and convert complex `cos/sin` of a real to `Real.cos/sin`
        have hexp :
            Complex.exp (t * x * Complex.I) =
              Complex.cos (t * x) + Complex.sin (t * x) * Complex.I := by
          -- `t * x * I = (t*x) * I` in `ℂ`
          simpa [mul_assoc] using (Complex.exp_mul_I (x := (t * x : ℂ)))
        -- expand using `hexp`, then rewrite `Complex.cos/sin` of a real via `Complex.ofReal_cos/sin`
        calc
          (g x : ℂ) * Complex.exp (t * x * Complex.I)
              = (g x : ℂ) * (Complex.cos (t * x) + Complex.sin (t * x) * Complex.I) := by
                    simp [hexp]
          _ = (g x : ℂ) * Complex.cos (t * x) + (g x : ℂ) * (Complex.sin (t * x) * Complex.I) := by
                simp [mul_add]
          _ = (g x : ℂ) * ((Real.cos (t * x) : ℂ)) +
                (g x : ℂ) * (((Real.sin (t * x) : ℂ)) * Complex.I) := by
                -- `Complex.cos (t*x) = (Real.cos (t*x) : ℂ)` and similarly for `sin`
                simp [Complex.ofReal_cos, Complex.ofReal_sin]
          _ = (g x * Real.cos (t * x) : ℂ) + (g x * Real.sin (t * x) : ℂ) * Complex.I := by
                -- reassociate and rewrite real scalar multiplication in `ℂ`
                ring
      -- integrability (bounded trig)
      have hgInt : Integrable (fun x : ℝ => (g x : ℂ)) gaussMeasure := by
        have : MemLp g 1 gaussMeasure :=
          hg.mono_exponent (μ := gaussMeasure) (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
        simpa using (memLp_one_iff_integrable.mp this).ofReal
      have hIntCos : Integrable (fun x : ℝ => (g x * Real.cos (t * x) : ℂ)) gaussMeasure := by
        refine hgInt.mul_bdd (c := (1 : ℝ)) (by fun_prop) ?_
        exact ae_of_all _ (fun x => by
          -- bound the norm of an `ofReal`
          have hnorm : ‖(Real.cos (t * x) : ℂ)‖ = |Real.cos (t * x)| := by
            simpa using (RCLike.norm_ofReal (K := ℂ) (Real.cos (t * x)))
          -- `|cos| ≤ 1` on `ℝ`
          have habs : |Real.cos (t * x)| ≤ (1 : ℝ) := Real.abs_cos_le_one (t * x)
          -- conclude
          -- goal: `‖(Real.cos (t * x) : ℂ)‖ ≤ 1`
          calc
            ‖(Real.cos (t * x) : ℂ)‖ = |Real.cos (t * x)| := hnorm
            _ ≤ (1 : ℝ) := habs)
      have hIntSin : Integrable (fun x : ℝ => ((g x * Real.sin (t * x) : ℂ) * Complex.I))
          gaussMeasure := by
        have : Integrable (fun x : ℝ => (g x * Real.sin (t * x) : ℂ)) gaussMeasure := by
          refine hgInt.mul_bdd (c := (1 : ℝ)) (by fun_prop) ?_
          exact ae_of_all _ (fun x => by
            have hnorm : ‖(Real.sin (t * x) : ℂ)‖ = |Real.sin (t * x)| := by
              simpa using (RCLike.norm_ofReal (K := ℂ) (Real.sin (t * x)))
            have habs : |Real.sin (t * x)| ≤ (1 : ℝ) := Real.abs_sin_le_one (t * x)
            calc
              ‖(Real.sin (t * x) : ℂ)‖ = |Real.sin (t * x)| := hnorm
              _ ≤ (1 : ℝ) := habs)
        simpa [mul_assoc] using this.mul_const Complex.I
      -- compute integral
      rw [hrepr]
      have hcosC :
          ∫ x : ℝ, (g x * Real.cos (t * x) : ℂ) ∂gaussMeasure = 0 := by
        -- cast the real identity `hcos0 t` into `ℂ`
        have hcast :
            (∫ x : ℝ, (g x * Real.cos (t * x) : ℂ) ∂gaussMeasure) =
              (↑(∫ x : ℝ, g x * Real.cos (t * x) ∂gaussMeasure) : ℂ) := by
          simpa using
            (integral_ofReal (μ := gaussMeasure) (f := fun x : ℝ => g x * Real.cos (t * x))
              (𝕜 := ℂ))
        -- finish without `simp` rewriting `Real.cos` into `Complex.cos`
        rw [hcast]
        simpa using congrArg (fun r : ℝ => (r : ℂ)) (hcos0 t)
      have hsinC :
          ∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) ∂gaussMeasure = 0 := by
        have hcast :
            (∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) ∂gaussMeasure) =
              (↑(∫ x : ℝ, g x * Real.sin (t * x) ∂gaussMeasure) : ℂ) := by
          simpa using
            (integral_ofReal (μ := gaussMeasure) (f := fun x : ℝ => g x * Real.sin (t * x))
              (𝕜 := ℂ))
        rw [hcast]
        simpa using congrArg (fun r : ℝ => (r : ℂ)) (hsin0 t)
      have hsinCI :
          ∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) * Complex.I ∂gaussMeasure = 0 := by
        -- pull out the constant `Complex.I`
        calc
          ∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) * Complex.I ∂gaussMeasure
              = (∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) ∂gaussMeasure) * Complex.I := by
                  simpa using
                    (integral_mul_const (μ := gaussMeasure) (r := (Complex.I))
                      (f := fun x : ℝ => (g x * Real.sin (t * x) : ℂ)))
          _ = 0 := by
                -- `hsinC` gives the integral is `0`, hence multiplying by `I` is still `0`
                rw [hsinC]
                simp
      -- now combine the two vanishing integrals
      calc
        (∫ x : ℝ,
              (g x * Real.cos (t * x) : ℂ) + (g x * Real.sin (t * x) : ℂ) * Complex.I
            ∂gaussMeasure)
            =
            (∫ x : ℝ, (g x * Real.cos (t * x) : ℂ) ∂gaussMeasure) +
              (∫ x : ℝ, (g x * Real.sin (t * x) : ℂ) * Complex.I ∂gaussMeasure) := by
              exact (integral_add hIntCos hIntSin)
        _ = 0 := by
              -- avoid rewriting `Real.cos/sin` into `Complex.cos/sin`
              rw [hcosC, hsinCI]
              simp
    -- finish
    rw [hpos, hneg]
    have hInt1 :
        Integrable (fun x : ℝ => ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I)) gaussMeasure :=
      by
        have htoReal : Integrable (fun x : ℝ => (ρpos x).toReal) gaussMeasure :=
          integrable_toReal_of_lintegral_ne_top hρpos_meas hLinPos
        have htoRealC : Integrable (fun x : ℝ => ((ρpos x).toReal : ℂ)) gaussMeasure :=
          htoReal.ofReal
        refine htoRealC.mul_bdd (c := (1 : ℝ)) (by fun_prop) ?_
        -- `‖exp((t*x)*I)‖ = 1`
        exact ae_of_all _ (fun x => by
          have hn : ‖Complex.exp (t * x * Complex.I)‖ = (1 : ℝ) := by
            simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I (t * x))
          exact le_of_eq hn)
    have hInt2 :
        Integrable (fun x : ℝ => ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I)) gaussMeasure :=
      by
        have htoReal : Integrable (fun x : ℝ => (ρneg x).toReal) gaussMeasure :=
          integrable_toReal_of_lintegral_ne_top hρneg_meas hLinNeg
        have htoRealC : Integrable (fun x : ℝ => ((ρneg x).toReal : ℂ)) gaussMeasure :=
          htoReal.ofReal
        refine htoRealC.mul_bdd (c := (1 : ℝ)) (by fun_prop) ?_
        exact ae_of_all _ (fun x => by
          have hn : ‖Complex.exp (t * x * Complex.I)‖ = (1 : ℝ) := by
            simpa [mul_assoc] using (Complex.norm_exp_ofReal_mul_I (t * x))
          exact le_of_eq hn)
    have :
        (∫ x : ℝ, ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) -
          (∫ x : ℝ, ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) =
          ∫ x : ℝ, (g x : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
      -- `integral_sub` gives `∫ (f - g) = ∫ f - ∫ g`; we use its symmetric form
      -- and then rewrite the integrand using `hdiff`.
      have hsub :
          (∫ x : ℝ, ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) -
              (∫ x : ℝ, ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) =
            ∫ x : ℝ,
                ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) -
                  ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure := by
        simpa using (integral_sub hInt1 hInt2).symm
      have hdiff' :
          (fun x : ℝ =>
              ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) -
                ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I)) =
            fun x : ℝ => (g x : ℂ) * Complex.exp (t * x * Complex.I) := by
        funext x
        -- evaluate the function identity `hdiff`
        simpa using congrArg (fun f => f x) hdiff
      -- rewrite the RHS integral using `hdiff'`
      simpa [hdiff'] using hsub
    -- finish from `hexp0` (the RHS integral vanishes)
    have hsub :
        (∫ x : ℝ, ((ρpos x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) -
            (∫ x : ℝ, ((ρneg x).toReal : ℂ) * Complex.exp (t * x * Complex.I) ∂gaussMeasure) =
          0 := by
      exact this.trans hexp0
    exact sub_eq_zero.mp hsub

  -- Extensionality by characteristic functions.
  have hEq : μpos = μneg :=
    Measure.ext_of_charFun (μ := μpos) (ν := μneg) (funext hchar)

  -- Convert equality of measures to a.e.-equality of densities.
  have hρ : ρpos =ᵐ[gaussMeasure] ρneg := by
    have hmeas_pos : AEMeasurable ρpos gaussMeasure := by fun_prop
    have hmeas_neg : AEMeasurable ρneg gaussMeasure := by fun_prop
    exact (MeasureTheory.withDensity_eq_iff (μ := gaussMeasure) (f := ρpos) (g := ρneg)
      hmeas_pos hmeas_neg hLinPos).1 (by simpa [μpos, μneg] using hEq)

  have hmax :
      (fun x : ℝ => max (g x) 0) =ᵐ[gaussMeasure] fun x : ℝ => max (-g x) 0 := by
    filter_upwards [hρ] with x hx
    have hx' : ENNReal.ofReal (max (g x) 0) = ENNReal.ofReal (max (-g x) 0) := by
      simpa [ρpos, ρneg] using hx
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 hx'

  -- pointwise conclusion
  refine hmax.mono ?_
  intro x hx
  by_cases hgx : 0 ≤ g x
  · have hpos : max (g x) 0 = g x := max_eq_left hgx
    have hneg : max (-g x) 0 = 0 := by
      have : -g x ≤ 0 := by nlinarith
      exact max_eq_right this
    -- rewrite the hypothesis `hx : max (g x) 0 = max (-g x) 0`
    simpa [hpos, hneg] using hx
  · have hgx' : g x ≤ 0 := le_of_not_ge hgx
    have hpos : max (g x) 0 = 0 := max_eq_right hgx'
    have hneg : max (-g x) 0 = -g x := by
      have : 0 ≤ -g x := by nlinarith
      exact max_eq_left this
    have h : -g x = 0 := by
      -- `hx` becomes `0 = -g x`
      simpa [hpos, hneg] using hx.symm
    simpa using (neg_eq_zero.mp h)

end PhysHermiteGauss

end

end PhysLean
