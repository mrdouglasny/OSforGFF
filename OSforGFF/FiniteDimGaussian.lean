/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite-dimensional Gaussian measures (characteristic function)

This module provides a small, reusable finite-dimensional Gaussian construction on
`EuclideanSpace ℝ n` (a.k.a. `PiLp 2 (fun _ : n => ℝ)`) together with its characteristic function.

It is meant as a prerequisite for the eventual (Bochner–)Minlos development: from a covariance
matrix on a finite set of test functions we obtain the corresponding Gaussian finite-dimensional
distribution and can compute its characteristic function.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

open MeasureTheory Complex

namespace OSforGFF.FiniteDimGaussian

noncomputable section

open ProbabilityTheory Matrix
open WithLp (toLp ofLp)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Standard Gaussian on `EuclideanSpace` -/

/-- The standard Gaussian measure on `EuclideanSpace ℝ n`, i.e. independent coordinates with law
`gaussianReal 0 1`, transported from the product space via `toLp 2`. -/
noncomputable def stdGaussian (n : Type*) [Fintype n] [DecidableEq n] :
    Measure (EuclideanSpace ℝ n) :=
  ((Measure.pi (fun _ : n => gaussianReal (0 : ℝ) (1 : ℝ≥0))).map (toLp (2 : ℝ≥0∞)))

instance : IsProbabilityMeasure (stdGaussian (n := n)) := by
  classical
  simpa [stdGaussian] using
    (Measure.isProbabilityMeasure_map (μ := Measure.pi (fun _ : n => gaussianReal (0 : ℝ) (1 : ℝ≥0)))
      (f := toLp (2 : ℝ≥0∞))
      ((by fun_prop : Measurable (toLp (2 : ℝ≥0∞))).aemeasurable))

lemma charFun_stdGaussian (t : EuclideanSpace ℝ n) :
    MeasureTheory.charFun (stdGaussian (n := n)) t =
      Complex.exp (-(1 / 2 : ℂ) * (‖t‖ ^ 2 : ℝ)) := by
  classical
  have hpi :
      MeasureTheory.charFun (stdGaussian (n := n)) t =
        ∏ i : n, MeasureTheory.charFun (gaussianReal (0 : ℝ) (1 : ℝ≥0)) (t i) := by
    simpa [stdGaussian] using
      (MeasureTheory.charFun_pi (μ := fun _ : n => gaussianReal (0 : ℝ) (1 : ℝ≥0)) (t := t))
  have hpi' :
      MeasureTheory.charFun (stdGaussian (n := n)) t =
        ∏ i : n, Complex.exp (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ)) := by
    simp [hpi, ProbabilityTheory.charFun_gaussianReal, sub_eq_add_neg, div_eq_mul_inv, mul_comm]
  have hexp :
      (∏ i : n, Complex.exp (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ))) =
        Complex.exp (∑ i : n, (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ))) := by
    simpa using
      (Complex.exp_sum (s := (Finset.univ : Finset n))
        (f := fun i : n => (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ)))).symm
  have hnorm : (∑ i : n, (t i) ^ 2) = (‖t‖ ^ 2 : ℝ) := by
    have : (‖t‖ ^ 2 : ℝ) = ∑ i : n, ‖t i‖ ^ 2 := by
      simpa using (PiLp.norm_sq_eq_of_L2 (β := fun _ : n => ℝ) t)
    simpa [Real.norm_eq_abs, sq_abs] using this.symm
  have hnormC : (∑ i : n, ((t i : ℝ) ^ 2 : ℂ)) = (‖t‖ ^ 2 : ℂ) := by
    simpa using (congrArg (fun x : ℝ => (x : ℂ)) hnorm)
  calc
    MeasureTheory.charFun (stdGaussian (n := n)) t
        = ∏ i : n, Complex.exp (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ)) := hpi'
    _ = Complex.exp (∑ i : n, (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ))) := hexp
    _ = Complex.exp (-(1 / 2 : ℂ) * (‖t‖ ^ 2 : ℝ)) := by
          have hfactor :
              (∑ i : n, (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ))) =
                (-(1 / 2 : ℂ)) * (∑ i : n, ((t i : ℝ) ^ 2 : ℂ)) := by
            classical
            simpa using
              (Finset.mul_sum (-(1 / 2 : ℂ)) (s := (Finset.univ : Finset n))
                (f := fun i : n => ((t i : ℝ) ^ 2 : ℂ))).symm
          have hexponent :
              (∑ i : n, (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ))) =
                (-(1 / 2 : ℂ)) * (‖t‖ ^ 2 : ℂ) := by
            calc
              (∑ i : n, (-(1 / 2 : ℂ) * ((t i : ℝ) ^ 2 : ℂ)))
                  = (-(1 / 2 : ℂ)) * (∑ i : n, ((t i : ℝ) ^ 2 : ℂ)) := hfactor
              _ = (-(1 / 2 : ℂ)) * (‖t‖ ^ 2 : ℂ) := by simp [hnormC]
          simpa using congrArg Complex.exp hexponent

/-! ## `Matrix.toEuclideanCLM` and adjoints -/

@[simp]
lemma adjoint_toEuclideanCLM (A : Matrix n n ℝ) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).adjoint =
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Aᴴ := by
  simpa [ContinuousLinearMap.star_eq_adjoint] using
    ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).map_star' A).symm

/-- The characteristic function commutes with pushforward along a continuous linear map, with the
adjoint acting on the argument. -/
lemma charFun_map_continuousLinearMap
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    (μ : Measure E) (L : E →L[ℝ] F) (t : F) :
    MeasureTheory.charFun (μ.map L) t = MeasureTheory.charFun μ (L.adjoint t) := by
  rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply]
  have hL : AEMeasurable L μ := (L.continuous.measurable.aemeasurable)
  have h_integrand :
      AEStronglyMeasurable (fun x : F => Complex.exp (⟪x, t⟫ * I)) (μ.map L) := by
    have : Measurable (fun x : F => Complex.exp (⟪x, t⟫ * I)) := by
      fun_prop
    exact this.aestronglyMeasurable
  rw [MeasureTheory.integral_map (hφ := hL) (hfm := h_integrand)]
  refine integral_congr_ae ?_
  filter_upwards with x
  congr 1
  simpa [mul_assoc] using (L.adjoint_inner_right x t).symm

/-! ## Gaussian with covariance matrix -/

/-- A (centered) Gaussian measure on `EuclideanSpace ℝ n` with covariance matrix `Σ`.

We choose `B` such that `Σ = Bᴴ * B` (possible for positive semidefinite `Σ`), then transport the
standard Gaussian by the continuous linear map associated to `Bᴴ`. -/
noncomputable def gaussianOfPosSemidef (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef) :
    Measure (EuclideanSpace ℝ n) :=
  let B : Matrix n n ℝ :=
    Classical.choose (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSigma.nonneg)
  (stdGaussian (n := n)).map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Bᴴ)

instance (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef) :
    IsProbabilityMeasure (gaussianOfPosSemidef (n := n) Sigma hSigma) := by
  let B : Matrix n n ℝ :=
    Classical.choose (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSigma.nonneg)
  simpa [gaussianOfPosSemidef, B] using
    (Measure.isProbabilityMeasure_map (μ := stdGaussian (n := n))
      (f := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Bᴴ)
      ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Bᴴ).continuous.measurable.aemeasurable))

lemma charFun_gaussianOfPosSemidef (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef)
    (t : EuclideanSpace ℝ n) :
    MeasureTheory.charFun (gaussianOfPosSemidef (n := n) Sigma hSigma) t =
      Complex.exp (-(1 / 2 : ℂ) * ⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ) := by
  classical
  set B : Matrix n n ℝ :=
    Classical.choose (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSigma.nonneg) with hB
  have hSigmaB : Sigma = Bᴴ * B := by
    simpa using
      (Classical.choose_spec (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hSigma.nonneg))
  set M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Bᴴ with hM
  have h_map :
      MeasureTheory.charFun ((stdGaussian (n := n)).map M) t =
        MeasureTheory.charFun (stdGaussian (n := n)) (M.adjoint t) :=
    charFun_map_continuousLinearMap (μ := stdGaussian (n := n)) (L := M) (t := t)
  have h0 : MeasureTheory.charFun (stdGaussian (n := n)) (M.adjoint t) =
      Complex.exp (-(1 / 2 : ℂ) * (‖M.adjoint t‖ ^ 2 : ℝ)) := by
    simpa using (charFun_stdGaussian (n := n) (t := M.adjoint t))
  have hnorm :
      (‖M.adjoint t‖ ^ 2 : ℝ) =
        ⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ := by
    have : (‖M.adjoint t‖ ^ 2 : ℝ) = ⟪M.adjoint t, M.adjoint t⟫_ℝ := by
      simp
    have h_inner :
        ⟪M.adjoint t, M.adjoint t⟫_ℝ = ⟪t, M (M.adjoint t)⟫_ℝ := by
      simpa using (M.adjoint_inner_left (x := M.adjoint t) (y := t))
    have hMM :
        M (M.adjoint t) = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t := by
      calc
        M (M.adjoint t)
            = (M * M.adjoint) t := by rfl
        _ = ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Bᴴ) *
              (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) B)) t := by
              simp [hM]
        _ = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (Bᴴ * B)) t := by
              simp
        _ = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t := by simp [hSigmaB]
    calc
      (‖M.adjoint t‖ ^ 2 : ℝ) = ⟪M.adjoint t, M.adjoint t⟫_ℝ := this
      _ = ⟪t, M (M.adjoint t)⟫_ℝ := h_inner
      _ = ⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ := by simp [hMM]
  have hgauss : gaussianOfPosSemidef (n := n) Sigma hSigma = (stdGaussian (n := n)).map M := by
    simp [gaussianOfPosSemidef, hB, hM]
  have hnormC :
      (‖M.adjoint t‖ ^ 2 : ℂ) =
        (⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ : ℂ) := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hnorm
  calc
    MeasureTheory.charFun (gaussianOfPosSemidef (n := n) Sigma hSigma) t
        = MeasureTheory.charFun ((stdGaussian (n := n)).map M) t := by simp [hgauss]
    _ = MeasureTheory.charFun (stdGaussian (n := n)) (M.adjoint t) := h_map
    _ = Complex.exp (-(1 / 2 : ℂ) * (‖M.adjoint t‖ ^ 2 : ℝ)) := h0
    _ = Complex.exp (-(1 / 2 : ℂ) * ⟪t, (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma) t⟫_ℝ) := by
          simp [hnormC]

end

end OSforGFF.FiniteDimGaussian
