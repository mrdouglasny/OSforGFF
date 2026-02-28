/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import OSforGFF.General.PositiveDefinite
import OSforGFF.General.GaussianRBF
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import OSforGFF.Measure.NuclearSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Minlos Theorem (Axiom) and Gaussian Measure Construction

Axiomatizes the Minlos theorem: a continuous positive definite functional on a nuclear
space is the characteristic functional of a unique probability measure on the dual.
Applied with the Gaussian characteristic functional exp(−½C(f,f)) to construct μ.

## Axiom

- `minlos_theorem`: existence and uniqueness (Gel'fand–Vilenkin Vol. 4)

## Main declarations

- `minlos_gaussian_construction`: Minlos + Gaussian CF → probability measure
- `gaussian_measure_symmetry`: covariance-preserving maps induce measure symmetries
-/

open Complex MeasureTheory Matrix
open BigOperators

noncomputable section

/-! ## Axioms in this file

- `minlos_theorem`: Minlos theorem for nuclear spaces (Gel'fand–Vilenkin Vol. 4)

The nuclear space axiom `schwartz_nuclear` is declared in `Measure.NuclearSpace`.
The Gaussian RBF positive-definiteness is proved in `General.GaussianRBF`.
-/

/-! ## Minlos Theorem -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

-- We need a measurable space structure on the weak dual
instance : MeasurableSpace (WeakDual ℝ E) := borel _

/-- **Minlos Theorem** (existence and uniqueness): On a nuclear locally convex space E,
    a continuous, positive definite, normalized functional Φ : E → ℂ is the characteristic
    functional of a unique probability measure μ on the topological dual E':

    Φ(f) = ∫_{E'} exp(i⟨f,ω⟩) dμ(ω)

    **Applications**:
    - For E = S(ℝᵈ) (Schwartz space), E' = S'(ℝᵈ) (tempered distributions)
    - Gaussian measures: Φ(f) = exp(-½⟨f, Cf⟩) with nuclear covariance C
    - Construction of the Gaussian Free Field

    **References**: Minlos (1959), Gel'fand-Vilenkin Vol. 4, Billingsley. -/
axiom minlos_theorem
  [NuclearSpace E]
  (Φ : E → ℂ)
  (h_continuous : Continuous Φ)
  (h_positive_definite : IsPositiveDefinite Φ)
  (h_normalized : Φ 0 = 1) :
  ∃! μ : ProbabilityMeasure (WeakDual ℝ E),
    ∀ f : E, Φ f = ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure

/-- Derived uniqueness: two probability measures whose characteristic functionals both
    equal a continuous, positive definite, normalized Φ must be equal.
    Used for Gaussian measure symmetry and sign-flip invariance. -/
theorem minlos_uniqueness
  [NuclearSpace E]
  {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
  (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
  {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
  (h₁ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
  (h₂ : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
  μ₁ = μ₂ := by
  obtain ⟨μ₀, _, huniq⟩ := minlos_theorem Φ hΦ_cont hΦ_pd hΦ_norm
  exact (huniq μ₁ (fun f => (h₁ f).symm)).trans (huniq μ₂ (fun f => (h₂ f).symm)).symm

/-! ## Applications to Gaussian Free Fields -/

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

/-- Application of Minlos theorem to Gaussian measures.
    If the covariance form can be realized as a squared norm via a linear embedding T into
    a real inner product space H, then the Gaussian characteristic functional Φ(f) = exp(-½⟨f, Cf⟩)
    satisfies the conditions of Minlos theorem, yielding a Gaussian probability measure on E'.

    **Note**: We require H to be an inner product space (not just normed) because the
    Gaussian RBF kernel is only positive definite for Hilbert spaces. -/
theorem minlos_gaussian_construction
  [NuclearSpace E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (_h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, gaussian_characteristic_functional covariance_form f =
              ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure) := by
  -- Prove the three Minlos hypotheses for the Gaussian CF
  have h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form) := by
    exact continuous_exp.comp (continuous_const.mul (continuous_ofReal.comp h_continuous))
  have h_cf_pd := gaussian_positive_definite_via_embedding T covariance_form h_eq
  have h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1 := by
    simp [gaussian_characteristic_functional, h_zero]
  -- Extract existence from ∃!
  obtain ⟨μ, hchar, _⟩ := minlos_theorem
    (gaussian_characteristic_functional covariance_form)
    h_cf_cont h_cf_pd h_cf_norm
  exact ⟨μ, hchar⟩

/-- The measure constructed by Minlos theorem for a Gaussian characteristic functional
    indeed has that functional as its characteristic function.

    This theorem makes explicit that the Gaussian measure μ constructed via Minlos
    satisfies: for any test function f,
    ∫ ω, exp(i⟨f,ω⟩) dμ(ω) = exp(-½⟨f,Cf⟩)

    This is the fundamental property connecting the abstract Minlos construction
    to the concrete Gaussian generating functional used in quantum field theory.

    **Note**: Requires H to be an inner product space for the Gaussian RBF positivity. -/
theorem gaussian_measure_characteristic_functional
  [NuclearSpace E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (T : E →ₗ[ℝ] H)
  (covariance_form : E → E → ℝ)
  (h_eq : ∀ f, covariance_form f f = (‖T f‖^2 : ℝ))
  (h_nuclear : True)
  (h_zero : covariance_form 0 0 = 0)
  (h_continuous : Continuous (fun f => covariance_form f f))
  : ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
    (∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
              gaussian_characteristic_functional covariance_form f) := by
  obtain ⟨μ, hchar⟩ := minlos_gaussian_construction T covariance_form h_eq h_nuclear h_zero h_continuous
  exact ⟨μ, fun f => (hchar f).symm⟩

/-! ## Symmetry Transfer from Characteristic Functional to Measure

The key insight: if a linear transformation preserves the characteristic functional,
then by Minlos uniqueness, the corresponding measure is invariant under the induced
action on the dual space.

This is crucial for establishing Euclidean invariance (OS2) of the GFF:
if the covariance is Euclidean-invariant, then exp(-½⟨gf, C(gf)⟩) = exp(-½⟨f, Cf⟩),
and by uniqueness the measure is Euclidean-invariant. -/

/-- Corollary for Gaussian measures: if the covariance form is invariant under g,
    then the Gaussian measure is invariant under the dual action of g.

    This directly implies OS2 (Euclidean invariance) for the GFF when g is a
    Euclidean transformation and the covariance satisfies C(gf, gh) = C(f, h).

    Note: Not used in the master theorem (OS2 is proved by direct change of variables).
    Kept as documentation of the alternative uniqueness-based approach. -/
theorem gaussian_measure_symmetry
  [NuclearSpace E]
  (covariance_form : E → E → ℝ)
  (h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form))
  (h_cf_pd : IsPositiveDefinite (gaussian_characteristic_functional covariance_form))
  (h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussian_characteristic_functional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
  -- The pushforward measure under the dual action
  (μ_push : ProbabilityMeasure (WeakDual ℝ E))
  (h_push_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ_push.toMeasure =
                          ∫ ω, Complex.exp (I * (ω (g f))) ∂μ.toMeasure)
  : μ_push = μ := by
  -- The Gaussian CF is g-invariant when covariance is
  have h_Φ_symm : ∀ f, gaussian_characteristic_functional covariance_form (g f) =
                       gaussian_characteristic_functional covariance_form f := by
    intro f
    simp only [gaussian_characteristic_functional, h_covar_symm]
  -- Apply uniqueness
  exact minlos_uniqueness h_cf_cont h_cf_pd h_cf_norm
    (fun f => by rw [h_push_char, h_char (g f), h_Φ_symm]) h_char

end
