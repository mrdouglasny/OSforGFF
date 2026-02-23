/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.FiniteDimGaussian
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-!
# `IsGaussian` for `OSforGFF.FiniteDimGaussian.gaussianOfPosSemidef`

Mathlib's `ProbabilityTheory.IsGaussian` is a *predicate* on measures.  Our file
`OSforGFF.FiniteDimGaussian` constructs finite-dimensional centered Gaussian measures from a
positive semidefinite covariance matrix and computes their characteristic functions.

This module shows that the constructed measures are `IsGaussian`, so we can
reuse mathlib's Gaussian API (covariance/characteristic-function theorems, ext lemmas, etc.).
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

open MeasureTheory Complex Matrix

namespace OSforGFF.FiniteDimGaussian

noncomputable section

open ProbabilityTheory
open WithLp (toLp ofLp)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The finite-dimensional Gaussian measure constructed from a positive semidefinite covariance
matrix is Gaussian in the sense of mathlib (`ProbabilityTheory.IsGaussian`). -/
lemma isGaussian_gaussianOfPosSemidef (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef) :
    ProbabilityTheory.IsGaussian (gaussianOfPosSemidef (n := n) Sigma hSigma) := by
  refine (ProbabilityTheory.isGaussian_iff_gaussian_charFun (μ := gaussianOfPosSemidef (n := n) Sigma hSigma)).2 ?_
  let A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) Sigma
  have hAadj : A.adjoint = A := by
    have hHerm : Sigmaᴴ = Sigma := hSigma.1.eq
    dsimp [A]
    rw [adjoint_toEuclideanCLM (n := n) (A := Sigma)]
    simpa [hHerm]
  let fLin : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun x y : EuclideanSpace ℝ n => ⟪x, A y⟫_ℝ)
      (by
        intro x x' y
        simp [inner_add_left])
      (by
        intro c x y
        simp [real_inner_smul_left])
      (by
        intro x y y'
        simp [A, inner_add_right])
      (by
        intro c x y
        simp [A, inner_smul_right])
  let f : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
    fLin.mkContinuous₂ ‖A‖ (by
      intro x y
      have h₁ : ‖⟪x, A y⟫_ℝ‖ ≤ ‖x‖ * ‖A y‖ := by
        exact norm_inner_le_norm x (A y)
      have h₂ : ‖A y‖ ≤ ‖A‖ * ‖y‖ := by
        exact A.le_opNorm y
      have h₃ : ‖x‖ * ‖A y‖ ≤ ‖x‖ * (‖A‖ * ‖y‖) := by
        gcongr
      calc
        ‖fLin x y‖ = ‖⟪x, A y⟫_ℝ‖ := by simp [fLin]
        _ ≤ ‖x‖ * ‖A y‖ := h₁
        _ ≤ ‖x‖ * (‖A‖ * ‖y‖) := h₃.trans_eq rfl
        _ = ‖A‖ * ‖x‖ * ‖y‖ := by ring
        _ ≤ ‖A‖ * ‖x‖ * ‖y‖ := le_rfl)
  refine ⟨0, f, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · refine ⟨fun x y => ?_⟩
      have : ⟪x, A y⟫_ℝ = ⟪y, A x⟫_ℝ := by
        calc
          ⟪x, A y⟫_ℝ = ⟪A y, x⟫_ℝ := (real_inner_comm _ _).symm
          _ = ⟪y, A.adjoint x⟫_ℝ := by
                simpa using (A.adjoint_inner_right (x := y) (y := x)).symm
          _ = ⟪y, A x⟫_ℝ := by simp [hAadj]
      simpa [ContinuousLinearMap.toBilinForm_apply, f, fLin] using this
    · refine ⟨fun x => ?_⟩
      have hx :
          f x x = ⟪x, A x⟫_ℝ := by
        simp [f, fLin]
      have hdot :
          ⟪x, A x⟫_ℝ = (Sigma *ᵥ ofLp x) ⬝ᵥ star (ofLp x) := by
        simp [A, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toEuclideanCLM]
      have hdot' :
          ⟪x, A x⟫_ℝ = star (ofLp x) ⬝ᵥ (Sigma *ᵥ ofLp x) := by
        simpa [dotProduct_comm] using hdot
      have hpos : 0 ≤ star (ofLp x) ⬝ᵥ (Sigma *ᵥ ofLp x) :=
        hSigma.dotProduct_mulVec_nonneg (ofLp x)
      simpa [hx, hdot'] using hpos
  · intro t
    have ht : f t t = ⟪t, A t⟫_ℝ := by
      simp [f, fLin]
    simpa [ht, f, fLin, sub_eq_add_neg, div_eq_mul_inv, A, mul_assoc, mul_comm, mul_left_comm] using
      (charFun_gaussianOfPosSemidef (n := n) Sigma hSigma t)

instance (Sigma : Matrix n n ℝ) (hSigma : Sigma.PosSemidef) :
    ProbabilityTheory.IsGaussian (gaussianOfPosSemidef (n := n) Sigma hSigma) :=
  isGaussian_gaussianOfPosSemidef (n := n) Sigma hSigma

end

end OSforGFF.FiniteDimGaussian
