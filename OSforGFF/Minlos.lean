/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import OSforGFF.PositiveDefinite
import OSforGFF.GaussianRBF

/-!
# Minlos (core lemmas)

This file contains **non-axiomatic** core lemmas used by both the axiomatic and (future) proved
versions of Minlos' theorem.

The axiomatic Minlos theorem and its Gaussian specialization live in `OSforGFF/MinlosAxiomatic.lean`.

## Main declarations

- `gaussian_characteristic_functional`: The Gaussian characteristic functional exp(-½C(f,f))
- `gaussian_rbf_pd_innerProduct`: Gaussian RBF is positive definite (proved in GaussianRBF.lean)
- `gaussian_positive_definite_via_embedding`: PD via Hilbert space embedding C(f,f) = ‖Tf‖²
-/

open Complex
open BigOperators

noncomputable section

/-! ## Gaussian characteristic functional -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For Gaussian measures, the characteristic functional has the special form
    Φ(f) = exp(-½⟨f, Cf⟩) where C is a nuclear covariance operator. -/
def gaussian_characteristic_functional
  (covariance_form : E → E → ℝ) (f : E) : ℂ :=
  Complex.exp (-(1/2 : ℂ) * (covariance_form f f))

/-- **Gaussian RBF kernel is positive definite on inner product spaces.**

    For an inner product space H, the function φ(h) = exp(-½‖h‖²) is positive definite.

    **Proof sketch** (not yet formalized):
    Using the inner product identity ‖x-y‖² = ‖x‖² + ‖y‖² - 2⟨x,y⟩, we get:
      exp(-½‖x-y‖²) = exp(-½‖x‖²) · exp(-½‖y‖²) · exp(⟨x,y⟩)

    The function exp(⟨x,y⟩) is positive definite because:
    1. The inner product ⟨·,·⟩ is a positive semidefinite kernel
    2. Exponentials of PSD kernels are PSD (via Taylor expansion and Schur product theorem)
    3. Products of PSD kernels are PSD

    **Note**: This is FALSE for general normed spaces. The Gaussian RBF exp(-‖x‖²)
    is positive definite on V iff V embeds isometrically into a Hilbert space
    (Schoenberg's theorem / Bretagnolle-Dacunha-Castelle-Krivine theorem).

    **PROVEN** in `OSforGFF/GaussianRBF.lean` using:
    - The inner product kernel is PD
    - Exponential preserves PD (via Hadamard series and Schur product theorem)
    - Factorization: exp(-½|x-y|²) = exp(-½|x|²)·exp(-½|y|²)·exp(⟨x,y⟩) -/
theorem gaussian_rbf_pd_innerProduct
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
  IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gaussian_rbf_pd_innerProduct_proof

/-- If covariance is realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional
    is positive definite.

    **Note**: We require H to be an inner product space (not just normed space)
    because the Gaussian RBF kernel is only guaranteed positive definite for
    Hilbert spaces, not general Banach spaces. -/
lemma gaussian_positive_definite_via_embedding
  {E H : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ)) :
  IsPositiveDefinite (fun f => Complex.exp (-(1/2 : ℂ) * (covariance_form f f))) := by
  -- Reduce to Gaussian RBF on H and precomposed with T
  have hPD_H := gaussian_rbf_pd_innerProduct (H := H)
  -- Compose with T and rewrite using h_eq
  intro m x c
  have repl : ∀ i j,
      covariance_form (x i - x j) (x i - x j)
      = (‖T (x i - x j)‖^2 : ℝ) := by
    intro i j; simpa using h_eq (x i - x j)
  have hlin : ∀ i j, T (x i - x j) = T (x i) - T (x j) := by
    intro i j; simp [LinearMap.map_sub]
  have hnorm : ∀ i j, (‖T (x i - x j)‖^2 : ℝ) = (‖T (x i) - T (x j)‖^2 : ℝ) := by
    intro i j; simp [hlin i j]
  -- Apply PD of Gaussian on H precomposed with T
  have hPD_comp :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i) - T (x j)‖^2 : ℝ)))).re := by
    simpa using (isPositiveDefinite_precomp_linear
      (ψ := fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) hPD_H T) m x c
  -- Rewrite differences inside T using linearity
  have hPD_comp1 :
    0 ≤ (∑ i, ∑ j,
      (starRingEnd ℂ) (c i) * c j *
        Complex.exp (-(1/2 : ℂ) * ((‖T (x i - x j)‖^2 : ℝ)))).re := by
    simpa [LinearMap.map_sub] using hPD_comp
  -- Finally rewrite norm-squared via covariance_form equality
  have : 0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j *
      Complex.exp (-(1/2 : ℂ) * (covariance_form (x i - x j) (x i - x j)))).re := by
    simpa [repl] using hPD_comp1
  exact this

end
