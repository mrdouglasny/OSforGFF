/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Tactic  -- gives `ext` and `simp` power
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Algebra.Order.Group.Unbundled.Abs

import OSforGFF.Spacetime.Basic
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Spacetime.ComplexTestFunction

/-!
# Generating Functional and Schwinger Functions

Defines the generating functional Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω) and
Schwinger n-point functions Sₙ(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩...⟨ω,fₙ⟩ dμ(ω).

For centered Gaussian measures: Z[J] = exp(−½⟨J,CJ⟩) and all Sₙ are
determined by Wick's theorem from the two-point function S₂ = C.
-/

open MeasureTheory Complex
open TopologicalSpace

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]
variable {d : ℕ}

/-! ## Schwinger Functions

The Schwinger functions S_n are the n-th moments of field operators φ(f₁)...φ(fₙ)
where φ(f) = ⟨ω, f⟩ is the field operator defined by pairing the field configuration
with a test function.

Following Glimm and Jaffe, these are the fundamental correlation functions:
S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

The Schwinger functions contain all the physics and satisfy the OS axioms.
They can be obtained from the generating functional via exponential series:
S_n(f₁,...,fₙ) = (-i)ⁿ (coefficient of (iJ)ⁿ/n! in Z[J])
-/

/-- The n-th Schwinger function: n-point correlation function of field operators.
    S_n(f₁,...,fₙ) = ∫ ⟨ω,f₁⟩ ⟨ω,f₂⟩ ... ⟨ω,fₙ⟩ dμ(ω)

    This is the fundamental object in constructive QFT - all physics is contained
    in the infinite sequence of Schwinger functions {S_n}_{n=1}^∞. -/
def SchwingerFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunction d)) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure

/-- The 1-point Schwinger function: the mean field -/
def SchwingerFunction₁ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 1 ![f]

/-- The 2-point Schwinger function: the covariance -/
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (f g : (SchwartzTestFunction d)) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]


/-- The Schwinger function equals the direct covariance integral for n=2 -/
lemma schwinger_eq_covariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (f g : (SchwartzTestFunction d)) :
  SchwingerFunction₂ dμ_config f g = ∫ ω, (distributionPairing ω f) * (distributionPairing ω g) ∂dμ_config.toMeasure := by
  unfold SchwingerFunction₂ SchwingerFunction
  -- The product over {0, 1} expands to (f 0) * (f 1) = f * g
  classical
  simp [Fin.prod_univ_two]

/-- Complex version of Schwinger functions for complex test functions -/
def SchwingerFunctionℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
  (f : Fin n → (SchwartzTestFunctionℂ d)) : ℂ :=
  ∫ ω, (∏ i, distributionPairingℂ_real ω (f i)) ∂dμ_config.toMeasure

/-- The complex 2-point Schwinger function for complex test functions.
    This is the natural extension of SchwingerFunction₂ to complex test functions. -/
def SchwingerFunctionℂ₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (φ ψ : (SchwartzTestFunctionℂ d)) : ℂ :=
  SchwingerFunctionℂ dμ_config 2 ![φ, ψ]

/-- Property that SchwingerFunctionℂ₂ is ℂ-bilinear in both arguments.
    This is a key property for Gaussian measures and essential for OS0 analyticity. -/
def CovarianceBilinear (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (c : ℂ) (φ₁ φ₂ ψ : (SchwartzTestFunctionℂ d)),
    SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ ∧
    SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂) = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂

/-- If the product pairing is integrable for all test functions, then the complex
    2-point Schwinger function is ℂ-bilinear in both arguments. -/
lemma CovarianceBilinear_of_integrable
  (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_int : ∀ (φ ψ : (SchwartzTestFunctionℂ d)),
    Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
      dμ_config.toMeasure) :
  CovarianceBilinear dμ_config := by
  classical
  intro c φ₁ φ₂ ψ
  -- Abbreviations for the integrands
  let u₁ : (FieldConfiguration d) → ℂ := fun ω => distributionPairingℂ_real ω φ₁
  let u₂ : (FieldConfiguration d) → ℂ := fun ω => distributionPairingℂ_real ω φ₂
  let v  : (FieldConfiguration d) → ℂ := fun ω => distributionPairingℂ_real ω ψ
  have hint₁ : Integrable (fun ω => u₁ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₁ ψ
  have hint₂ : Integrable (fun ω => u₂ ω * v ω) dμ_config.toMeasure := by simpa using h_int φ₂ ψ
  have hint₃ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := by simpa using h_int φ₁ φ₂

  -- 1) Scalar multiplication in the first argument
  have h_smul_left_integrand :
      (fun ω => distributionPairingℂ_real ω (c • φ₁) * distributionPairingℂ_real ω ψ)
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ (0 : (SchwartzTestFunctionℂ d)) c 0
    -- dp ω (c•φ₁) = c * dp ω φ₁
    have h' : distributionPairingℂ_real ω (c • φ₁) = c * distributionPairingℂ_real ω φ₁ := by
      simpa using h
    -- Multiply by the second factor and reassociate
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h1 :
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    -- Use scalar pull-out from the integral
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config (c • φ₁) ψ
          = ∫ ω, distributionPairingℂ_real ω (c • φ₁) * distributionPairingℂ_real ω ψ ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_left_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]

  -- 2) Additivity in the first argument
  have h_add_left_integrand :
      (fun ω => distributionPairingℂ_real ω (φ₁ + φ₂) * distributionPairingℂ_real ω ψ)
      = (fun ω => u₁ ω * v ω + u₂ ω * v ω) := by
    funext ω
    have h := pairing_linear_combo ω φ₁ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂ_real ω (φ₁ + φ₂)
              = distributionPairingℂ_real ω φ₁ + distributionPairingℂ_real ω φ₂ := by
      simpa using h
    rw [h']
    ring

  have hsum_left : ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := by
    simpa using (integral_add (hf := hint₁) (hg := hint₂))
  have h2 :
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
    calc
      SchwingerFunctionℂ₂ dμ_config (φ₁ + φ₂) ψ
          = ∫ ω, (u₁ ω * v ω + u₂ ω * v ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_left_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₂ ω * v ω ∂dμ_config.toMeasure := hsum_left
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₂ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two, Matrix.cons_val_zero]

  -- 3) Scalar multiplication in the second argument
  have h_smul_right_integrand :
      (fun ω => distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (c • ψ))
      = (fun ω => c • (u₁ ω * v ω)) := by
    funext ω
    have h := pairing_linear_combo ω ψ (0 : (SchwartzTestFunctionℂ d)) c 0
    have h' : distributionPairingℂ_real ω (c • ψ) = c * distributionPairingℂ_real ω ψ := by
      simpa using h
    rw [h']
    simp [u₁, v, smul_eq_mul]
    ring
  have h3 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ) = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
    have hlin : ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure
                = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := by
      simpa using (integral_smul (μ := dμ_config.toMeasure)
        (f := fun ω => u₁ ω * v ω) c)
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (c • ψ)
          = ∫ ω, distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (c • ψ) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two]
      _ = ∫ ω, c • (u₁ ω * v ω) ∂dμ_config.toMeasure := by
            simp [h_smul_right_integrand]
      _ = c • ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure := hlin
      _ = c • SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, v, Fin.prod_univ_two]
      _ = c * SchwingerFunctionℂ₂ dμ_config φ₁ ψ := by
            rw [smul_eq_mul]

  -- 4) Additivity in the second argument
  have h_add_right_integrand :
      (fun ω => distributionPairingℂ_real ω φ₁ * distributionPairingℂ_real ω (ψ + φ₂))
      = (fun ω => u₁ ω * v ω + u₁ ω * u₂ ω) := by
    funext ω
    have h := pairing_linear_combo ω ψ φ₂ (1 : ℂ) (1 : ℂ)
    have h' : distributionPairingℂ_real ω (ψ + φ₂)
              = distributionPairingℂ_real ω ψ + distributionPairingℂ_real ω φ₂ := by
      simpa using h
    rw [h']
    ring

  have hsum_right : ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure
      = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := by
    have hint₁₂ : Integrable (fun ω => u₁ ω * u₂ ω) dμ_config.toMeasure := hint₃
    simpa using (integral_add (hf := hint₁) (hg := hint₁₂))
  have h4 :
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
        = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
    calc
      SchwingerFunctionℂ₂ dμ_config φ₁ (ψ + φ₂)
          = ∫ ω, (u₁ ω * v ω + u₁ ω * u₂ ω) ∂dμ_config.toMeasure := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two, h_add_right_integrand]
      _ = ∫ ω, u₁ ω * v ω ∂dμ_config.toMeasure + ∫ ω, u₁ ω * u₂ ω ∂dμ_config.toMeasure := hsum_right
      _ = SchwingerFunctionℂ₂ dμ_config φ₁ ψ + SchwingerFunctionℂ₂ dμ_config φ₁ φ₂ := by
            simp [SchwingerFunctionℂ₂, SchwingerFunctionℂ, u₁, u₂, v, Fin.prod_univ_two, Matrix.cons_val_zero]

  -- Bundle the four identities
  exact And.intro h1 (And.intro h2 (And.intro h3 h4))
