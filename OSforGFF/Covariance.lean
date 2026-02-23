/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

-- Import our basic definitions
import OSforGFF.Basic
import OSforGFF.Euclidean
import OSforGFF.DiscreteSymmetry
import OSforGFF.Schwinger
import OSforGFF.FunctionalAnalysis
import OSforGFF.CovarianceMomentum
import OSforGFF.FourierTransforms
import OSforGFF.Parseval

/-!
# Free Covariance for Gaussian Free Field

This file contains Fourier analysis infrastructure and position-space covariance properties
for the Gaussian Free Field. The momentum space propagator and basic covariance definitions
are in CovarianceMomentum.lean.

## Main Definitions

- `heatKernelMomentum`: Heat kernel in momentum space
- `freeCovarianceℂ_regulated`, `freeCovarianceℂ`: complex covariance forms (regulated / Bessel)

## Key Results

- `freeCovariance_euclidean_invariant`: Euclidean invariance of the covariance
- `covariance_timeReflection_invariant`: Time reflection invariance
-/

open MeasureTheory Complex Real Filter
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

/-! ## Axioms in this file

This file contains no axioms.
-/

noncomputable section
/-! ### Fourier analysis infrastructure -/

/-- The heat kernel in momentum space. This is the result of integrating the full propagator over the time-component of momentum. -/
noncomputable def heatKernelMomentum (m : ℝ) (t : ℝ) (k_spatial : SpatialCoords) : ℝ :=
  Real.exp (-t * Real.sqrt (‖k_spatial‖^2 + m^2)) / Real.sqrt (‖k_spatial‖^2 + m^2)

/- ** (Parseval for Covariance - Position Space formulation with regulator):**
    The fundamental Parseval identity relating the regulated covariance bilinear form to
    momentum-space propagator. The regulator exp(-α(2π)²‖k‖²) ensures absolute convergence.

    Uses `freePropagatorMomentum_mathlib` which accounts for the 2π factor in Mathlib's Fourier convention.
    Defined in FourierTransforms.lean as `parseval_covariance_schwartz_regulated`. -/
/-- **(Time Reflection Change of Variables):**
    Integrating a function over spacetime is unchanged when both variables are composed with
    geometric time reflection.  This packages the measure-preserving property of time reflection
    together with Fubini's theorem for later use in reflection-positivity arguments. -/
lemma double_integral_timeReflection
  (G : SpaceTime → SpaceTime → ℂ) :
  ∫ x, ∫ y, G (QFT.timeReflection x) (QFT.timeReflection y) ∂volume ∂volume
    = ∫ x, ∫ y, G x y ∂volume ∂volume := by
  have hmp := QFT.timeReflection_measurePreserving
  have hmeas := QFT.timeReflectionLE.toMeasurableEquiv.measurableEmbedding
  -- Apply change of variables for inner integral first
  have h_inner : ∀ x, ∫ y, G x (QFT.timeReflection y) = ∫ y, G x y :=
    fun x => hmp.integral_comp hmeas (fun y => G x y)
  simp_rw [h_inner]
  -- Then apply change of variables for outer integral
  exact hmp.integral_comp hmeas (fun x => ∫ y, G x y)

/-- Specialized time-reflection change of variables for covariance-type kernels.
    This packages the combination of `double_integral_timeReflection` and the
    observation that `compTimeReflection` is just composition with
    `timeReflection`, so we can reuse the general measure-preserving axiom
    without re-establishing integrability each time. -/
lemma double_integral_timeReflection_covariance
  (m : ℝ) (f g : TestFunctionℂ) :
  ∫ x, ∫ y,
      (QFT.compTimeReflection f) x * (freeCovariance m x y : ℂ) * g y ∂volume ∂volume
    = ∫ x, ∫ y,
        f x * (freeCovariance m (QFT.timeReflection x) (QFT.timeReflection y) : ℂ)
          * (QFT.compTimeReflection g) y ∂volume ∂volume := by
  -- compTimeReflection h x = h (timeReflectionCLM x) = h (timeReflection x)
  have h_comp : ∀ h : TestFunctionℂ, ∀ x, (QFT.compTimeReflection h) x = h (QFT.timeReflection x) := by
    intro h x
    simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
    rfl  -- timeReflectionCLM x = timeReflection x by definition
  -- Rewrite both sides using the definition of compTimeReflection
  simp_rw [h_comp]
  -- Now goal is: ∫∫ f(Θx) * C(x,y) * g(y) = ∫∫ f(x) * C(Θx, Θy) * g(Θy)
  -- timeReflection is an involution: Θ ∘ Θ = id
  have hinv : ∀ z, QFT.timeReflection (QFT.timeReflection z) = z := by
    intro z
    exact QFT.timeReflectionLE.left_inv z
  -- Transform RHS using double_integral_timeReflection (in reverse direction)
  -- After substitution x' = Θx, y' = Θy: RHS = ∫∫ f(Θx') * C(x', y') * g(y')
  rw [← double_integral_timeReflection (fun x y => f (QFT.timeReflection x) * (freeCovariance m x y : ℂ) * g y)]
  -- Use Θ∘Θ = id to simplify f(Θ(Θx)) = f(x)
  simp only [hinv]

/-! ### Reflection Positivity for Free Covariance

For real test functions supported on positive time (t > 0), the cross-covariance
∫∫ (Θf)(x) C(x,y) f(y) dx dy ≥ 0 where Θ is time reflection.

Mathematical justification: In momentum space, the free covariance factorizes as
C(x,y) = ∫ e^{ik·(x-y)} / (k² + m²) dk. For functions with positive time support,
the time integral factorizes via contour integration, yielding an exponential
e^{-ω|t|} factor (where ω = √(|p|² + m²)) which ensures the cross-term is positive.

This is the key input for Osterwalder-Schrader reflection positivity (OS3).

**PROVEN:** See `QFT.freeCovariance_reflection_positive_bilinear` in CovarianceRP.lean,
which uses the direct momentum representation approach (RPProof namespace). -/


/-! ### Complex bilinear form on test functions

The following section develops the bilinear structure of the covariance form.
All results assume `m > 0` (positive mass), which is required for integrability.

We use `freeCovarianceℂ_bilinear_integrable` from `CovarianceMomentum.lean`. -/

/-- Integrability of the covariance kernel evaluated on a time-reflected test function.
    This follows directly from `freeCovarianceℂ_bilinear_integrable` since `compTimeReflection`
    maps test functions to test functions. -/
lemma integrable_compTimeReflection_covariance
  (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
  Integrable (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflection f) p.1 * (freeCovariance m p.1 p.2 : ℂ) * f p.2)
    (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  exact freeCovarianceℂ_bilinear_integrable m (QFT.compTimeReflection f) f


/-- Relationship between compTimeReflection of toComplex and compTimeReflectionReal:
    they agree pointwise as complex values. -/
lemma compTimeReflection_toComplex_eq_ofReal
  (f : TestFunction) (x : SpaceTime) :
  (QFT.compTimeReflection (toComplex f)) x = ((QFT.compTimeReflectionReal f) x : ℂ) := by
  simp only [QFT.compTimeReflection, QFT.compTimeReflectionReal,
    SchwartzMap.compCLM_apply, Function.comp_apply, toComplex_apply]

/-- Integrability of the real covariance kernel obtained from a real test function. -/
lemma integrable_real_covariance_kernel
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  Integrable (fun p : SpaceTime × SpaceTime =>
      (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2)
    (volume.prod volume) := by
  -- Reduce to the complex-valued integrand and take real parts.
  let F : SpaceTime × SpaceTime → ℂ := fun p =>
    (QFT.compTimeReflection (toComplex f)) p.1
      * (freeCovariance m p.1 p.2 : ℂ)
      * (toComplex f) p.2
  have hF : Integrable F (volume.prod volume) := by
    -- `integrable_compTimeReflection_covariance` is stated with the same integrand.
    -- Avoid `simp` here (it can be expensive in this project).
    change
      Integrable (fun p : SpaceTime × SpaceTime =>
        (QFT.compTimeReflection (toComplex f)) p.1
          * (freeCovariance m p.1 p.2 : ℂ)
          * (toComplex f) p.2) (volume.prod volume)
    exact integrable_compTimeReflection_covariance (m := m) (f := toComplex f)
  have hF_re : Integrable (fun p => (F p).re) (volume.prod volume) := hF.re
  -- The complex integrand is real-valued (as a cast), so its real part is the desired real integrand.
  have h_re : (fun p => (F p).re) =
      fun p => (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2 := by
    ext p
    -- Avoid aggressive `simp` (it may blow up); do a small, explicit rewrite instead.
    -- First rewrite the complex integrand as a single `ofReal`.
    have h_ofReal :
        F p =
          ((QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2 : ℂ) := by
      -- Unfold `F` and rewrite every factor as an `ofReal`.
      dsimp [F]
      rw [compTimeReflection_toComplex_eq_ofReal (f := f) (x := p.1)]
      -- Now everything is an `ofReal`, so we can reassociate and combine.
      simp only [toComplex_apply, mul_assoc]
    -- Now take real parts.
    -- (We keep simplification minimal to avoid recursion-depth issues.)
    have := congrArg Complex.re h_ofReal
    simpa only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] using this
  simpa [h_re] using hF_re

/-- ** (Real-Complex Integral Correspondence):**
  The real integral with compTimeReflectionReal equals the real part of the
  corresponding complex integral after complexification.

  **Proof idea**: The complex integrand equals `(r x y : ℂ)` where `r` is the real integrand
  (using `compTimeReflection_toComplex_eq_ofReal` and `toComplex_apply`).
  For real-valued integrands, the `.re` of the complex integral equals the real integral
  via `integral_ofReal_eq` applied twice. -/
lemma real_integral_eq_complex_re
  (m : ℝ) [Fact (0 < m)] (f : TestFunction) :
  ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y ∂volume ∂volume
    = (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
        * (toComplex f) y ∂volume ∂volume).re := by
  classical
  -- Rewrite both iterated integrals as integrals over the product measure.
  let r : SpaceTime × SpaceTime → ℝ := fun p =>
    (QFT.compTimeReflectionReal f) p.1 * freeCovariance m p.1 p.2 * f p.2
  let c : SpaceTime × SpaceTime → ℂ := fun p =>
    (QFT.compTimeReflection (toComplex f)) p.1
      * (freeCovariance m p.1 p.2 : ℂ)
      * (toComplex f) p.2
  have hr : Integrable r (volume.prod volume) := by
    simpa [r] using integrable_real_covariance_kernel (m := m) f
  have hc : Integrable c (volume.prod volume) := by
    -- Avoid `simp` here (it can be expensive in this project).
    change
      Integrable (fun p : SpaceTime × SpaceTime =>
        (QFT.compTimeReflection (toComplex f)) p.1
          * (freeCovariance m p.1 p.2 : ℂ)
          * (toComplex f) p.2) (volume.prod volume)
    exact integrable_compTimeReflection_covariance (m := m) (f := toComplex f)
  have hL :
      (∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y ∂volume ∂volume)
        = ∫ p, r p ∂(volume.prod volume) := by
    simpa [r] using (MeasureTheory.integral_prod (f := r) hr).symm
  have hR :
      (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
          * (toComplex f) y ∂volume ∂volume).re
        = (∫ p, c p ∂(volume.prod volume)).re := by
    -- `MeasureTheory.integral_prod` gives the product/iterated integral equality; take real parts.
    -- Avoid `simp` here; just unfold `c` by definitional reduction.
    have := congrArg Complex.re (MeasureTheory.integral_prod (f := c) hc).symm
    exact this
  have h_eq : ∀ p, c p = (r p : ℂ) := by
    intro p
    -- Unfold and rewrite all factors as `ofReal`.
    dsimp [c, r]
    rw [compTimeReflection_toComplex_eq_ofReal (f := f) (x := p.1)]
    simp only [toComplex_apply, mul_assoc, Complex.ofReal_mul]
  have h_cast_re :
      (∫ p, c p ∂(volume.prod volume)).re = ∫ p, r p ∂(volume.prod volume) := by
    calc
      (∫ p, c p ∂(volume.prod volume)).re
          = (∫ p, (r p : ℂ) ∂(volume.prod volume)).re := by
              refine congrArg Complex.re (integral_congr_ae ?_)
              exact Filter.Eventually.of_forall h_eq
      _ = ∫ p, r p ∂(volume.prod volume) := by
            -- `integral_ofReal` is the standard Mathlib lemma.
            simpa using congrArg Complex.re
              (integral_ofReal (μ := (volume.prod volume)) (f := r))
  -- Put everything together.
  -- (The goal is LHS = RHS.re.)
  calc
    ∫ x, ∫ y, (QFT.compTimeReflectionReal f) x * freeCovariance m x y * f y ∂volume ∂volume
        = ∫ p, r p ∂(volume.prod volume) := hL
    _ = (∫ p, c p ∂(volume.prod volume)).re := h_cast_re.symm
    _ = (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance m x y : ℂ)
            * (toComplex f) y ∂volume ∂volume).re := by
          exact hR.symm

/-- ** (Complex Conjugate Identity for Real Functions):**
  For real-valued test functions lifted to complex, the complex conjugate equals the original.
  This allows us to match the Parseval identity which uses starRingEnd. -/
lemma toComplex_star_eq
  (f : TestFunction) (x : SpaceTime) :
  starRingEnd ℂ ((toComplex f) x) = (toComplex f) x := by
  -- toComplex f x = (f x : ℂ) by definition
  simp only [toComplex_apply]
  -- The conjugate of a real number (lifted to ℂ) is itself
  exact Complex.conj_ofReal (f x)

/-- The time-reflected complexification of a real test function remains real-valued. -/
lemma compTimeReflection_toComplex_star_eq
  (f : TestFunction) (x : SpaceTime) :
  starRingEnd ℂ ((QFT.compTimeReflection (toComplex f)) x)
    = (QFT.compTimeReflection (toComplex f)) x := by
  -- compTimeReflection is composition with timeReflectionCLM
  simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
  -- Now we have (toComplex f) (QFT.timeReflectionCLM x)
  -- Use the fact that toComplex produces real values
  exact toComplex_star_eq f (QFT.timeReflectionCLM x)

-- and theorem spatial_reduction_to_heat_kernel that depended on them

-- freeCovariancePositive, freeCovariance_reflection_positive, freeCovarianceReflectionPositiveMomentum,
-- freeCovariance_positive_definite, freeCovariance_positive_definite_regulated, fourierTransform_timeReflection,
-- covarianceBilinearForm, covarianceBilinearForm_continuous_basic, covarianceBilinearForm_continuous,
-- LinearIsometry.inner_adjoint_eq_inv

/-! ## Euclidean Invariance -/

/-- Euclidean invariance of the free covariance.
    Since freeCovariance only depends on ‖x - y‖ (via the Bessel form), and Euclidean
    transformations preserve distances, this follows immediately. -/
theorem freeCovariance_euclidean_invariant (m : ℝ)
  (g : QFT.E) (x y : SpaceTime) :
  freeCovariance m (QFT.act g x) (QFT.act g y) = freeCovariance m x y := by
  -- freeCovariance = freeCovarianceBessel only depends on ‖x - y‖
  -- Euclidean transformations preserve this distance
  unfold freeCovariance freeCovarianceBessel
  -- QFT.act g x - QFT.act g y = g.R (x - y) where g.R is a linear isometry
  have h_diff : QFT.act g x - QFT.act g y = g.R (x - y) := by simp [QFT.act]
  simp only [h_diff, g.R.norm_map]

/-- Time reflection as an element of the Euclidean group (rotation with no translation). -/
def timeReflectionE : QFT.E := ⟨QFT.timeReflectionLE.toLinearIsometry, 0⟩

/-- The Euclidean action of timeReflectionE equals timeReflection. -/
lemma act_timeReflectionE (x : SpaceTime) : QFT.act timeReflectionE x = QFT.timeReflection x := by
  simp only [timeReflectionE, QFT.act, add_zero, LinearIsometryEquiv.coe_toLinearIsometry]
  rfl

/-- ** (Time Reflection Invariance - Position Space):**
  The position-space covariance kernel is invariant under geometric time reflection.
  This follows from general Euclidean invariance since time reflection is in O(4). -/
lemma covariance_timeReflection_invariant (m : ℝ) :
    ∀ x y, freeCovariance m (QFT.timeReflection x) (QFT.timeReflection y) = freeCovariance m x y := by
  intro x y
  rw [← act_timeReflectionE x, ← act_timeReflectionE y]
  exact freeCovariance_euclidean_invariant m timeReflectionE x y

/-! ## Complex Extension

Note: `freeCovarianceℂ_bilinear` is defined in Parseval.lean (imported above).
The following lemmas prove properties of this bilinear form. -/

/-- For each fixed `x`, the inner integral in the complex bilinear form is absolutely integrable.
    This follows from product integrability (`freeCovarianceℂ_bilinear_integrable`) plus Fubini. -/
lemma freeCovarianceℂ_bilinear_inner_integrable
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  Integrable (fun x => ∫ y, (f x) * (freeCovariance m x y) * (g y) ∂volume) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- For each fixed `x`, the inner integral defining the bilinear form is integrable in `y`.
    Together with the previous lemma, this allows iterated integration.
    Follows from product integrability via Fubini (`Integrable.prod_right_ae`). -/
lemma freeCovarianceℂ_bilinear_slice_integrable
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
  ∀ᵐ x ∂volume, Integrable (fun y => (f x) * (freeCovariance m x y) * (g y)) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.prod_right_ae

/-- Generalized bilinearity in the first argument: scalar multiplication and addition combined. -/
theorem freeCovarianceℂ_bilinear_add_smul_left
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f₁ f₂ g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m (c • f₁ + f₂) g
      = c * freeCovarianceℂ_bilinear m f₁ g + freeCovarianceℂ_bilinear m f₂ g := by
  classical
  -- Expand the definition and introduce convenient abbreviations for the
  -- outer integrands that appear in the bilinear form.
  simp only [freeCovarianceℂ_bilinear]
  set F := fun x : SpaceTime =>
    ∫ y, ((c • f₁ + f₂) x) * (freeCovariance m x y : ℂ) * (g y) ∂volume
  set F₁ := fun x : SpaceTime =>
    ∫ y, f₁ x * (freeCovariance m x y : ℂ) * (g y) ∂volume
  set F₂ := fun x : SpaceTime =>
    ∫ y, f₂ x * (freeCovariance m x y : ℂ) * (g y) ∂volume
  have hF : Integrable F volume :=
    freeCovarianceℂ_bilinear_inner_integrable m (c • f₁ + f₂) g
  have hF₁ : Integrable F₁ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₁ g
  have hF₂ : Integrable F₂ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₂ g
  -- For almost every x we can expand the inner integral using linearity.
  have h_add_smul_ae :
      F =ᵐ[volume] fun x => c * F₁ x + F₂ x := by
    have h_slice₁ :=
      freeCovarianceℂ_bilinear_slice_integrable m f₁ g
    have h_slice₂ :=
      freeCovarianceℂ_bilinear_slice_integrable m f₂ g
    refine (h_slice₁.and h_slice₂).mono ?_
    intro x hx
    rcases hx with ⟨hf₁x, hf₂x⟩
    have hfun :
        (fun y => ((c • f₁ + f₂) x) * (freeCovariance m x y : ℂ) * (g y))
          = fun y =>
              c * (f₁ x * (freeCovariance m x y : ℂ) * (g y))
                + f₂ x * (freeCovariance m x y : ℂ) * (g y) := by
      funext y
      -- (c • f₁ + f₂) x = c * f₁ x + f₂ x
      have h1 : (c • f₁ + f₂) x = c * f₁ x + f₂ x := rfl
      rw [h1]
      ring
    calc
      F x
          = ∫ y,
              ((c • f₁ + f₂) x) * (freeCovariance m x y) * (g y) ∂volume := rfl
      _ = ∫ y,
            (c * (f₁ x * (freeCovariance m x y) * (g y)) +
              f₂ x * (freeCovariance m x y) * (g y)) ∂volume := by
            rw [hfun]
      _ = c * F₁ x + F₂ x := by
            have h_const_out : ∫ y, c * (f₁ x * (freeCovariance m x y) * (g y)) ∂volume
                             = c * ∫ y, (f₁ x * (freeCovariance m x y) * (g y)) ∂volume := by
              exact MeasureTheory.integral_const_mul c _
            rw [integral_add, h_const_out]
            · apply Integrable.const_mul
              exact hf₁x
            · exact hf₂x
  have h_int_eq : ∫ x, F x ∂volume = ∫ x, (c * F₁ x + F₂ x) ∂volume :=
    integral_congr_ae h_add_smul_ae
  -- Apply linearity of the outer integral.
  have hF₁_smul : Integrable (fun x => c * F₁ x) volume := by
    apply Integrable.const_mul
    exact hF₁
  have h_sum := integral_add hF₁_smul hF₂
  calc
    ∫ x, F x ∂volume
        = ∫ x, (c * F₁ x + F₂ x) ∂volume := h_int_eq
    _ = (∫ x, c * F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := h_sum
    _ = c * (∫ x, F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := by rw [MeasureTheory.integral_const_mul]

theorem freeCovarianceℂ_bilinear_add_left
  (m : ℝ) [Fact (0 < m)] (f₁ f₂ g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m (f₁ + f₂) g
      = freeCovarianceℂ_bilinear m f₁ g + freeCovarianceℂ_bilinear m f₂ g := by
  -- Use the generalized lemma with c = 1
  have h := freeCovarianceℂ_bilinear_add_smul_left m 1 f₁ f₂ g
  -- Simplify 1 • f₁ = f₁ and 1 * (...) = (...)
  simp only [one_smul, one_mul] at h
  exact h

theorem freeCovarianceℂ_bilinear_smul_left
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m (c • f) g = c * freeCovarianceℂ_bilinear m f g := by
  -- Use the generalized lemma with f₁ = f and f₂ = 0
  have h := freeCovarianceℂ_bilinear_add_smul_left m c f 0 g
  -- Simplify: c • f + 0 = c • f
  rw [add_zero] at h
  -- Need to show freeCovarianceℂ_bilinear m 0 g = 0
  have zero_bilinear : freeCovarianceℂ_bilinear m 0 g = 0 := by
    unfold freeCovarianceℂ_bilinear
    -- 0 x = 0, so the integrand becomes 0 * ... = 0
    have h : ∀ x y, (0 : TestFunctionℂ) x * (freeCovariance m x y : ℂ) * g y = 0 := by
      intro x y
      -- (0 : TestFunctionℂ) x = 0
      have : (0 : TestFunctionℂ) x = 0 := rfl
      rw [this]
      simp only [zero_mul]
    simp_rw [h]
    rw [integral_zero, integral_zero]
  rw [zero_bilinear, add_zero] at h
  exact h

/-- Symmetry of the complex bilinear form: swapping arguments gives the same result. -/
theorem freeCovarianceℂ_bilinear_symm
  (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m f g = freeCovarianceℂ_bilinear m g f := by
  unfold freeCovarianceℂ_bilinear
  -- Use the symmetry of the underlying covariance kernel freeCovariance m x y = freeCovariance m y x
  -- Apply change of variables: swap x ↔ y in the integration domain
  have h : ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume
         = ∫ y, ∫ x, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume := by
    -- Swap the order of integration (follows from Fubini's theorem)
    -- We have the necessary integrability condition from freeCovarianceℂ_bilinear_integrable
    apply MeasureTheory.integral_integral_swap
    -- The integrand is integrable on the product space
    exact freeCovarianceℂ_bilinear_integrable m f g
  rw [h]
  -- Now apply variable relabeling: swap variable names x ↔ y in the second integral
  -- ∫ y, ∫ x, f x * freeCovariance m x y * g y = ∫ x, ∫ y, f y * freeCovariance m y x * g x
  have relabel : ∫ y, ∫ x, (f x) * (freeCovariance m x y) * (g y) ∂volume ∂volume
               = ∫ x, ∫ y, (f y) * (freeCovariance m y x) * (g x) ∂volume ∂volume := by
    -- This is just renaming bound variables, which is always valid
    rfl
  rw [relabel]
  -- Now use symmetry of freeCovariance: freeCovariance m y x = freeCovariance m x y
  congr 1 with x
  congr 1 with y
  rw [freeCovariance_symmetric m y x]
  -- Rearrange: g x * freeCovariance m x y * f y = g x * freeCovariance m x y * f y
  ring

theorem freeCovarianceℂ_bilinear_smul_right
  (m : ℝ) [Fact (0 < m)] (c : ℂ) (f g : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m f (c • g) = c * freeCovarianceℂ_bilinear m f g := by
  -- Use symmetry to convert right scalar multiplication to left scalar multiplication
  -- freeCovarianceℂ_bilinear m f (c • g) = freeCovarianceℂ_bilinear m (c • g) f
  rw [freeCovarianceℂ_bilinear_symm m f (c • g)]
  -- Apply left scalar multiplication: freeCovarianceℂ_bilinear m (c • g) f = c * freeCovarianceℂ_bilinear m g f
  rw [freeCovarianceℂ_bilinear_smul_left m c g f]
  -- Use symmetry again: c * freeCovarianceℂ_bilinear m g f = c * freeCovarianceℂ_bilinear m f g
  rw [freeCovarianceℂ_bilinear_symm m g f]

theorem freeCovarianceℂ_bilinear_add_right
  (m : ℝ) [Fact (0 < m)] (f g₁ g₂ : TestFunctionℂ) :
    freeCovarianceℂ_bilinear m f (g₁ + g₂)
      = freeCovarianceℂ_bilinear m f g₁ + freeCovarianceℂ_bilinear m f g₂ := by
  -- Use symmetry to convert right addition to left addition
  -- freeCovarianceℂ_bilinear m f (g₁ + g₂) = freeCovarianceℂ_bilinear m (g₁ + g₂) f
  rw [freeCovarianceℂ_bilinear_symm m f (g₁ + g₂)]
  -- Apply left addition: freeCovarianceℂ_bilinear m (g₁ + g₂) f = freeCovarianceℂ_bilinear m g₁ f + freeCovarianceℂ_bilinear m g₂ f
  rw [freeCovarianceℂ_bilinear_add_left m g₁ g₂ f]
  -- Use symmetry on each term: freeCovarianceℂ_bilinear m g₁ f + freeCovarianceℂ_bilinear m g₂ f = freeCovarianceℂ_bilinear m f g₁ + freeCovarianceℂ_bilinear m f g₂
  rw [freeCovarianceℂ_bilinear_symm m g₁ f, freeCovarianceℂ_bilinear_symm m g₂ f]

/-- Complex extension of the covariance for complex test functions (using regulated Fourier form). -/
def freeCovarianceℂ_regulated (α : ℝ) (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (freeCovariance_regulated α m x y) * (starRingEnd ℂ (g y)) ∂volume ∂volume

/-- The regulated complex covariance is positive definite for any α > 0. -/
theorem freeCovarianceℂ_regulated_positive (α : ℝ) (hα : 0 < α) (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
  0 ≤ (freeCovarianceℂ_regulated α m f f).re := by
  unfold freeCovarianceℂ_regulated
  rw [parseval_covariance_schwartz_regulated α hα m f]
  apply MeasureTheory.integral_nonneg
  intro k
  apply mul_nonneg
  · apply mul_nonneg
    · exact Real.exp_nonneg _
    · exact sq_nonneg _
  · exact freePropagatorMomentum_mathlib_nonneg m (Fact.out) k

/-- Complex extension of the covariance for complex test functions (limit form via Bessel). -/
def freeCovarianceℂ (m : ℝ) (f g : TestFunctionℂ) : ℂ :=
  ∫ x, ∫ y, (f x) * (freeCovariance m x y) * (starRingEnd ℂ (g y)) ∂volume ∂volume

/-- The complex covariance (Bessel form) is positive definite. -/
theorem freeCovarianceℂ_positive (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    0 ≤ (freeCovarianceℂ m f f).re := by
  -- The regulated form converges to the Bessel form as α → 0⁺
  -- Use the specialized f = f version which leverages momentum-space DCT
  have h_tendsto := bilinear_covariance_regulated_tendsto_self m f
  -- This is the same as: freeCovarianceℂ_regulated α m f f → freeCovarianceℂ m f f
  have h_tendsto' : Filter.Tendsto (fun α => freeCovarianceℂ_regulated α m f f)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (freeCovarianceℂ m f f)) := h_tendsto
  -- By continuity of .re, the real parts also converge
  have h_tendsto_re : Filter.Tendsto (fun α => (freeCovarianceℂ_regulated α m f f).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (freeCovarianceℂ m f f).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp h_tendsto'
  -- The regulated forms are nonnegative for α > 0
  have h_nonneg : ∀ᶠ α in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ (freeCovarianceℂ_regulated α m f f).re := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact freeCovarianceℂ_regulated_positive α hα m f
  -- Pass through the limit
  exact ge_of_tendsto h_tendsto_re h_nonneg

/-- **(Parseval for Bessel Covariance):**
    The Parseval identity for the well-defined Bessel form of the covariance.
    This directly relates the position-space covariance integral to the momentum-space integral.

    Note: Unlike the regulated form, this uses freeCovariance (Bessel K₁ form) which is
    well-defined pointwise. The equality holds because the Bessel form equals the limit
    of the regulated forms. -/
theorem parseval_covariance_schwartz_bessel (m : ℝ) [Fact (0 < m)] (f : TestFunctionℂ) :
    (freeCovarianceℂ m f f).re
    = ∫ k, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖^2 * freePropagatorMomentum_mathlib m k ∂volume := by
  -- Strategy: Use uniqueness of limits
  -- 1. bilinear_covariance_regulated_tendsto_self: lim (regulated) = Bessel (in ℂ) for f = f case
  -- 2. parseval_covariance_schwartz_correct: lim (regulated).re = momentum (in ℝ)
  -- 3. By continuity of .re: (Bessel).re = momentum

  -- The Bessel form is defined as freeCovarianceℂ
  -- freeCovarianceℂ m f f = ∫∫ f(x) * C(x,y) * conj(f(y))
  have h_bessel_eq : freeCovarianceℂ m f f =
      ∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (f y)) := rfl

  -- The complex bilinear form converges to the Bessel form
  -- Use the specialized f = f version which leverages momentum-space DCT
  have h_tendsto_complex := bilinear_covariance_regulated_tendsto_self m f

  -- The .re of the regulated form converges to the momentum integral
  have h_tendsto_re := parseval_covariance_schwartz_correct m f

  -- By continuity of .re, the limit of (regulated).re equals (limit of regulated).re
  have h_re_continuous : Continuous Complex.re := Complex.continuous_re

  -- The .re of the limit equals the limit of .re
  have h_re_tendsto : Filter.Tendsto
      (fun α => (∫ x, ∫ y, f x * (freeCovariance_regulated α m x y : ℂ) * (starRingEnd ℂ (f y))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, ∫ y, f x * (freeCovariance m x y : ℂ) * (starRingEnd ℂ (f y))).re) :=
    h_re_continuous.continuousAt.tendsto.comp h_tendsto_complex

  -- By uniqueness of limits in ℝ, the two limits are equal
  have h_unique := tendsto_nhds_unique h_re_tendsto h_tendsto_re
  rw [h_bessel_eq]
  exact h_unique

/-! ## OS Properties -/
