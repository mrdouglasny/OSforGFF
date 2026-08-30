/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Measure.GaussianFreeField
import OSforGFF.Measure.Construct
import OSforGFF.Measure.Minlos
import OSforGFF.Measure.IsGaussian
import OSforGFF.Schwinger.Defs
import OSforGFF.Schwinger.GaussianMoments

/-!
# LEGACY — unused measure-layer and Schwinger-layer declarations (off the build graph)

**Status: legacy.** Proven declarations from the measure-construction and Schwinger-function
layers that no declaration on the build graph consumes. Preserved here with full proofs;
**not on the root import graph**. Verify in isolation with

    lake env lean OSforGFF/Legacy/UnusedMeasureSchwinger.lean

Former `private` markers are dropped for archival visibility. Declarations keep their
original namespaces; each block re-declares the `open`/`variable` context of its source file.
One tiny helper is DUPLICATED rather than moved: `conj_cexp_real` remains `private` in
`Measure/Minlos.lean` (a live lemma there still uses it), so this file carries its own copy
for the moved `gaussian_rbf_pd_bochner`.

## Supersession map

From `Measure/GaussianFreeField.lean` (the alternative OS0 program — the proof used by
`OS.Master` is `OS.OS0_Analyticity`'s holomorphic-integral route):
- `OS0_alt.bilin_sum_sum`, `OS0_alt.GJcov_bilin`, `OS0_alt.gaussian_satisfies_OS0` — the
  closed OS0_alt cluster: quadratic-form expansion of the Gaussian generating functional.
- `CovarianceContinuous` — a continuity predicate never consumed by any hypothesis.

From `Measure/Construct.lean`:
- `gaussian_pairing_square_integrable_real` (moved 2026-08-30) — the diagonal real case
  of pairing-square integrability; the OS1 chain uses
  `gaussian_pairing_product_integrable_free_2point` directly.
- `structure CovarianceFunction` — abstract covariance packaging, never instantiated; the
  construction works with `freeCovarianceFormR`/`GFFPropagator` directly.

From `Measure/Minlos.lean`:
- `gaussian_cf_im_zero` (formerly `private`) — used only by `gaussian_rbf_pd_bochner`.
- `gaussian_rbf_pd_bochner` — RBF-kernel positive-definiteness in the bochner sense; the
  construction route uses `gaussian_positive_definite_bochner` (embedding form) instead.
- `gaussian_measure_symmetry` — symmetry transfer from the characteristic functional to the
  measure; the OS2 proof invokes `minlos_gaussian_uniqueness` directly.

From `Measure/IsGaussian.lean`:
- `GFFIsGaussian.gaussian_pairing_product_integrable_free_core` — restatement of
  `gaussian_pairing_product_integrable_free_2point`, which consumers use directly.

From `Schwinger/Defs.lean`:
- `schwinger_eq_mean` (moved 2026-08-30) — `S₁ = GJMean`; no consumer, the OS chain works
  with `SchwingerFunction₂` and the generating functional.
- `schwinger_vanishes_centered` — vanishing of the 1-point function for centered measures.
- `IsGaussianMeasure` — a Gaussianity predicate superseded by `isGaussianGJ`
  (`Measure/Construct.lean`).
- the whole former `namespace AQFT_exponential_series` (all formerly `private`):
  `expIPartial`, `expIPartial_tendsto`, `expIPartial_norm_le`, `prod_const_pow`,
  `schwinger_eq_integral_pow` — the exponential-series expansion of the generating
  functional; never wired into the OS chain. Note: `schwinger_eq_integral_pow` is stated
  with the dimension hard-coded to `d = 4`, from the original 4D development.
- `SpaceTimeProduct`, `TestFunctionProduct` — n-fold product-space test-function types
  (a closed pair: the latter is the former's only consumer); the distribution framework
  they were built for never materialized on-graph.

From `Schwinger/GaussianMoments.lean`:
- `GaussianMoments.gaussian_complex_pairing_abs_sq_integrable` — the |⟨ω,φ⟩|² base
  estimate; consumers use `gaussian_pairing_product_integrable_free_2point`, which
  re-derives it inline.
-/

/-! ### From `Measure/GaussianFreeField.lean` -/

section GaussianFreeField

open MeasureTheory Complex
open TopologicalSpace SchwartzMap
open scoped BigOperators
open Finset

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-! ### OS0_alt Namespace

Alternative proof of OS0 for Gaussian measures via the explicit quadratic form expansion.
The main proof used by `OS.Master` is in `OS.OS0_Analyticity` (holomorphic integral theorem).
-/

namespace OS0_alt

/-- Helper lemma for bilinear expansion with finite sums -/
lemma bilin_sum_sum {E : Type*} [AddCommMonoid E] [Module ℂ E]
  (B : LinearMap.BilinMap ℂ E ℂ) (n : ℕ) (J : Fin n → E) (z : Fin n → ℂ) :
  B (∑ i, z i • J i) (∑ j, z j • J j) = ∑ i, ∑ j, z i * z j * B (J i) (J j) := by
  -- Use bilinearity: B is linear in both arguments
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  -- Swap order of summation: ∑ x, z x * ∑ x_1, ... = ∑ i, ∑ j, ...
  rw [Finset.sum_comm]
  -- Convert smul to multiplication and use distributivity
  simp only [smul_eq_mul]
  -- Use distributivity for multiplication over sums
  congr 1; ext x; rw [Finset.mul_sum]
  -- Rearrange multiplication: z x * (z i * B ...) = z i * z x * B ...
  congr 1; ext i; ring

end OS0_alt

/-- Assumption: The complex covariance is continuous bilinear -/
def CovarianceContinuous (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (J K : SchwartzTestFunctionℂ d), Continuous (fun z : ℂ =>
    SchwingerFunctionℂ₂ dμ_config (z • J) K)

/-! ## OS0: Analyticity for Gaussian Measures (OLD PROOF - in OS0_alt namespace)

The key insight is that for Gaussian measures, the generating functional
Z[∑ᵢ zᵢJᵢ] = exp(-½⟨∑ᵢ zᵢJᵢ, C(∑ⱼ zⱼJ⟩) = exp(-½ ∑ᵢⱼ zᵢzⱼ⟨Jᵢ, CJ⟩)
is the exponential of a polynomial in the complex variables zᵢ, hence entire.

Note: The primary proof is in `OSforGFF.OS.OS0_Analyticity`.
-/

namespace OS0_alt

def GJcov_bilin (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_bilinear : CovarianceBilinear dμ_config) : LinearMap.BilinMap ℂ (SchwartzTestFunctionℂ d) ℂ :=
  LinearMap.mk₂ ℂ
    (fun x y => SchwingerFunctionℂ₂ dμ_config x y)
    (by intro x x' y  -- additivity in the 1st arg
        exact (h_bilinear 1 x x' y).2.1)
    (by intro a x y   -- homogeneity in the 1st arg
        exact (h_bilinear a x 0 y).1)
    (by intro x y y'  -- additivity in the 2nd arg
        have h := (h_bilinear 1 x y y').2.2.2
        -- h: SchwingerFunctionℂ₂ dμ_config x (y' + y) = SchwingerFunctionℂ₂ dμ_config x y' + SchwingerFunctionℂ₂ dμ_config x y
        -- We need: SchwingerFunctionℂ₂ dμ_config x (y + y') = SchwingerFunctionℂ₂ dμ_config x y + SchwingerFunctionℂ₂ dμ_config x y'
        simp only [add_comm y' y, add_comm (SchwingerFunctionℂ₂ dμ_config x y') _] at h
        exact h)
    (by intro a x y   -- homogeneity in the 2nd arg
        exact (h_bilinear a x 0 y).2.2.1)

omit [Fact (2 ≤ d)] in
theorem gaussian_satisfies_OS0
  (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_gaussian : isGaussianGJ dμ_config)
  (h_bilinear : CovarianceBilinear dμ_config)
  : OS0_Analyticity dμ_config := by
  intro n J

  -- Extract the Gaussian form: Z[f] = exp(-½⟨f, Cf⟩)
  have h_form : ∀ (f : SchwartzTestFunctionℂ d),
      GJGeneratingFunctionalℂ dμ_config f = Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config f f) :=
    h_gaussian.2

  -- Rewrite the generating functional using Gaussian form
  have h_rewrite : (fun z : Fin n → ℂ => GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) =
                   (fun z => Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i))) := by
    funext z
    exact h_form (∑ i, z i • J i)

  rw [h_rewrite]

  -- Show exp(-½ * quadratic_form) is analytic
  apply AnalyticOn.cexp
  apply AnalyticOn.mul
  · exact analyticOn_const

  · -- Show the quadratic form is analytic by expanding via bilinearity
    let B := GJcov_bilin dμ_config h_bilinear

    -- Expand quadratic form: ⟨∑ᵢ zᵢJᵢ, C(∑ⱼ zⱼJ⟩) = ∑ᵢⱼ zᵢzⱼ⟨Jᵢ, CJ⟩
    have h_expansion : (fun z : Fin n → ℂ => SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i)) =
                       (fun z => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
      funext z
      have h_eq : B (∑ i, z i • J i) (∑ i, z i • J i) = SchwingerFunctionℂ₂ dμ_config (∑ i, z i • J i) (∑ i, z i • J i) := rfl
      rw [← h_eq]
      exact bilin_sum_sum B n J z

    rw [h_expansion]

    -- Double sum of monomials is analytic
    -- Each monomial z_i * z_j is analytic, and finite sums of analytic functions are analytic
    have h_sum_analytic : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
      -- Each term z_i * z_j * constant is analytic
      have h_monomial : ∀ i j, AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
        intro i j
        -- Rewrite as constant times polynomial
        have h_factor : (fun z : Fin n → ℂ => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
                        (fun z => SchwingerFunctionℂ₂ dμ_config (J i) (J j) * (z i * z j)) := by
          funext z; ring
        rw [h_factor]

        apply AnalyticOnNhd.mul
        · exact analyticOnNhd_const
        · -- z_i * z_j is analytic as product of coordinate projections
          have coord_i : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z i) Set.univ := by
            exact (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ).analyticOnNhd _
          have coord_j : AnalyticOnNhd ℂ (fun z : Fin n → ℂ => z j) Set.univ := by
            exact (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ).analyticOnNhd _
          exact AnalyticOnNhd.mul coord_i coord_j

      -- Apply finite sum analyticity twice by decomposing the sum
      -- First for outer sum
      have h_outer_sum : ∀ i, AnalyticOnNhd ℂ (fun z : Fin n → ℂ => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) Set.univ := by
        intro i
        -- Apply sum analyticity to inner sum over j
        have : (fun z : Fin n → ℂ => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
               (∑ j : Fin n, fun z => z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
          ext z; simp [Finset.sum_apply]
        rw [this]
        apply Finset.analyticOnNhd_sum
        intro j _
        exact h_monomial i j

      -- Now apply for the outer sum
      have : (fun z : Fin n → ℂ => ∑ i, ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) =
             (∑ i : Fin n, fun z => ∑ j, z i * z j * SchwingerFunctionℂ₂ dμ_config (J i) (J j)) := by
        ext z; simp [Finset.sum_apply]
      rw [this]
      apply Finset.analyticOnNhd_sum
      intro i _
      exact h_outer_sum i

    -- Convert from AnalyticOnNhd to AnalyticOn
    exact h_sum_analytic.analyticOn

end OS0_alt

end

end GaussianFreeField

/-! ### From `Measure/Construct.lean` -/

section Construct

open MeasureTheory Complex QFT ProbabilityTheory OSforGFF
open TopologicalSpace SchwartzMap

noncomputable section

/-- A covariance function on test functions that determines the Gaussian measure -/
structure CovarianceFunction (d : ℕ) where
  covar : SchwartzTestFunctionℂ d → SchwartzTestFunctionℂ d → ℂ
  symmetric : ∀ f g, covar f g = (starRingEnd ℂ) (covar g f)
  bilinear_left : ∀ c f₁ f₂ g, covar (c • f₁ + f₂) g = c * covar f₁ g + covar f₂ g
  bilinear_right : ∀ f c g₁ g₂, covar f (c • g₁ + g₂) = (starRingEnd ℂ) c * covar f g₁ + covar f g₂
  positive_semidefinite : ∀ f, 0 ≤ (covar f f).re
  bounded : ∃ M > 0, ∀ f, ‖covar f f‖ ≤ M * (∫ x, ‖f x‖ ∂volume) * (∫ x, ‖f x‖^2 ∂volume)^(1/2)

end

end Construct

/-! ### From `Measure/Minlos.lean` -/

section Minlos

open Complex MeasureTheory Matrix TopologicalSpace
open BigOperators

noncomputable section

/-- Helper: exp of a purely-real complex argument is self-conjugate.
    (Duplicated from `Measure/Minlos.lean`, where it remains `private` in service of a
    live lemma.) -/
lemma conj_cexp_real (z : ℂ) (h : z.im = 0) :
    starRingEnd ℂ (Complex.exp z) = Complex.exp z := by
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp [h])
  rw [hz, ← Complex.ofReal_exp]; exact Complex.conj_ofReal _

/-- The Gaussian CF argument -(1/2)*r is real for real r. -/
lemma gaussian_cf_im_zero (r : ℝ) :
    (-(1/2 : ℂ) * (r : ℂ)).im = 0 := by
  simp [Complex.mul_im, Complex.neg_im, Complex.ofReal_im]

/-- The Gaussian RBF kernel is positive definite in the bochner sense.
    The hermitian condition follows from ‖-h‖ = ‖h‖. -/
theorem gaussian_rbf_pd_bochner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] :
    IsPositiveDefinite (fun h : H => Complex.exp (-(1/2 : ℂ) * (‖h‖^2 : ℝ))) :=
  gff4d_to_bochner_pd gaussian_rbf_pd_innerProduct (fun h => by
    simp only [norm_neg]; exact (conj_cexp_real _ (gaussian_cf_im_zero _)).symm)

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- Corollary for Gaussian measures: if the covariance form is invariant under g,
    then the Gaussian measure is invariant under the dual action of g. -/
theorem gaussian_measure_symmetry
  [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
  (covariance_form : E → E → ℝ)
  (h_cf_cont : Continuous (gaussian_characteristic_functional covariance_form))
  (h_cf_pd : IsPositiveDefinite (gaussian_characteristic_functional covariance_form))
  (h_cf_norm : gaussian_characteristic_functional covariance_form 0 = 1)
  (μ : ProbabilityMeasure (WeakDual ℝ E))
  (h_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ.toMeasure =
                     gaussian_characteristic_functional covariance_form f)
  (g : E →L[ℝ] E)
  (h_covar_symm : ∀ f : E, covariance_form (g f) (g f) = covariance_form f f)
  (μ_push : ProbabilityMeasure (WeakDual ℝ E))
  (h_push_char : ∀ f : E, ∫ ω, Complex.exp (I * (ω f)) ∂μ_push.toMeasure =
                          ∫ ω, Complex.exp (I * (ω (g f))) ∂μ.toMeasure)
  : μ_push = μ := by
  have h_Φ_symm : ∀ f, gaussian_characteristic_functional covariance_form (g f) =
                       gaussian_characteristic_functional covariance_form f := by
    intro f
    simp only [gaussian_characteristic_functional, h_covar_symm]
  exact minlos_uniqueness h_cf_cont h_cf_pd h_cf_norm
    (fun f => by rw [h_push_char, h_char (g f), h_Φ_symm]) h_char


end

end Minlos

/-! ### From `Measure/IsGaussian.lean` -/

section IsGaussian

open MeasureTheory Complex QFT OSforGFF

noncomputable section

namespace GFFIsGaussian

variable {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]

/-- For the Gaussian Free Field measure, the product of two complex pairings with test functions
    is integrable. Uses the direct 2-point theorem from GaussianMoments. -/
lemma gaussian_pairing_product_integrable_free_core
    (φ ψ : SchwartzTestFunctionℂ d) :
    Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
      (gaussianFreeField_free m).toMeasure :=
  gaussian_pairing_product_integrable_free_2point m φ ψ

end GFFIsGaussian

end

end IsGaussian

/-! ### From `Schwinger/Defs.lean` -/

section SchwingerDefs

open MeasureTheory Complex
open TopologicalSpace

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]
variable {d : ℕ}

/-- The Schwinger function equals the GJ mean for n=1 (from `Schwinger/Defs.lean`,
    moved 2026-08-30). -/
lemma schwinger_eq_mean (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (f : (SchwartzTestFunction d)) :
  SchwingerFunction₁ dμ_config f = GJMean dμ_config f := by
  unfold SchwingerFunction₁ SchwingerFunction GJMean
  classical
  simp

/-- For centered measures (zero mean), the 1-point function vanishes -/
lemma schwinger_vanishes_centered (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_centered : ∀ f : (SchwartzTestFunction d), GJMean dμ_config f = 0) (f : (SchwartzTestFunction d)) :
  SchwingerFunction₁ dμ_config f = 0 := by
  rw [schwinger_eq_mean]
  exact h_centered f

/-! ## Exponential Series Connection to Generating Functional

The key insight: Instead of functional derivatives, we use the constructive exponential series:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω) = ∑_{n=0}^∞ (i)^n/n! * S_n(J,...,J)

This approach is more elementary and constructive than functional derivatives.
-/
/-- A (centered) Gaussian field measure: the generating functional is an exponential of a quadratic form. -/
def IsGaussianMeasure (dμ : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (Cov : (SchwartzTestFunction d) → (SchwartzTestFunction d) → ℝ),
    ∀ J : (SchwartzTestFunction d),
      GJGeneratingFunctional dμ J = Complex.exp ((-(1 : ℂ) / 2) * (Cov J J : ℂ))


/-
  === Exponential series for Z[J] via Dominated Convergence (along a ray) ===

  We prove:
    Z[J] = ∑ (i)^n / n! * S_n(J,…,J),

  by expanding exp(i⟨ω,J⟩) pointwise, bounding partial sums by exp(|⟨ω,J⟩|),
  and swapping ∫ and limit. This requires only an along‑ray exponential‑moment
  hypothesis. We package that as a simple Prop and then derive your theorem.
-/

open BigOperators MeasureTheory Complex

noncomputable section
namespace AQFT_exponential_series

/-- Finite Taylor partial sum of the exponential `exp(i x)` (complex valued). -/
def expIPartial (N : ℕ) (x : ℝ) : ℂ :=
  (Finset.range (N+1)).sum (fun n =>
    (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))

/-- Pointwise limit of the partial sums `expIPartial N x` is `exp(i x)`. -/
lemma expIPartial_tendsto (x : ℝ) :
  Filter.Tendsto (fun N => expIPartial N x) Filter.atTop (nhds (Complex.exp (Complex.I * (x : ℂ)))) := by
  classical
  -- Power series for the complex exponential at z = i * x
  -- Use the Banach algebra version of the exponential series has-sum.
  have hsum :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (𝔸 := ℂ)
      (x := (Complex.I * (x : ℂ))))
  -- Re-express terms to match our expIPartial integrand
  have hsum' : HasSum (fun n : ℕ =>
      (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))
      (Complex.exp (Complex.I * (x : ℂ))) := by
    -- Rewrite ((I * x)^n)/(n!) and (·)•(·) into our summand shape
    --   (n! : ℂ)⁻¹ • (I * x)^n = I^n * x^n / (n!)
    simpa [mul_pow, div_eq_mul_inv, smul_eq_mul,
           mul_comm, mul_left_comm, mul_assoc, Complex.exp_eq_exp_ℂ]
      using hsum
  -- Partial sums over range N tend to the sum
  have htend := hsum'.tendsto_sum_nat
  -- Compose with the shift N ↦ N+1 so we get range (N+1)
  have hshift : Filter.Tendsto (fun N : ℕ => N + 1) Filter.atTop Filter.atTop := by
    simpa using (Filter.tendsto_add_atTop_nat 1)
  -- Our definition uses range (N+1), align it and conclude
  have hsum_def :
      (fun N => expIPartial N x)
        = (fun N => (Finset.range (N+1)).sum
              (fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ))) := by
    funext N; simp [expIPartial]
  -- Final: tendsto of our partial sums
  simpa [hsum_def, Function.comp_def] using htend.comp hshift

lemma expIPartial_norm_le (x : ℝ) (N : ℕ) :
  ‖expIPartial N x‖ ≤ Real.exp (|x|) := by
  classical
  -- 1) Triangle inequality on the finite sum
  have h₁ :
      ‖expIPartial N x‖
        ≤ (Finset.range (N+1)).sum
            (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖) := by
    simpa [expIPartial] using
      (norm_sum_le (s := Finset.range (N+1))
        (f := fun n => (Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)))

  -- 2) Bound each term by (|x|^n)/n! and sum
  have h_term_le :
      ∀ n, ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖
            ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    -- Use multiplicativity of the norm and basic computations via simp
    -- ‖I^n‖ = 1, ‖(x:ℂ)^n‖ = |x|^n, ‖(n! : ℂ)‖ = n!
    simp [norm_pow, div_eq_mul_inv, norm_inv]

  have h₂ :
      (Finset.range (N+1)).sum
          (fun n => ‖(Complex.I : ℂ) ^ n * (x : ℂ) ^ n / (n.factorial : ℂ)‖)
        ≤ (Finset.range (N+1)).sum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ)) := by
    exact Finset.sum_le_sum (fun n _hn => h_term_le n)

  -- 3) Partial sums of ∑ |x|^n / n! are bounded by exp |x|
  have hsumR :
      HasSum (fun n : ℕ => (|x| : ℝ) ^ n / (n.factorial : ℝ))
             (Real.exp (|x|)) := by
    -- Banach algebra exponential series over ℝ at x = |x|
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, Real.exp_eq_exp_ℝ]
      using (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (𝔸 := ℝ) (x := (|x|)))

  have h_nonneg :
      ∀ n, 0 ≤ (|x| : ℝ) ^ n / (n.factorial : ℝ) := by
    intro n
    exact div_nonneg (pow_nonneg (abs_nonneg x) n) (by exact Nat.cast_nonneg' n.factorial)

  have h₃ :
      (Finset.range (N+1)).sum (fun n => (|x| : ℝ) ^ n / (n.factorial : ℝ))
        ≤ Real.exp (|x|) := by
    -- Use the modern Summable.sum_le_tsum
    have := (hsumR.summable.sum_le_tsum (s := Finset.range (N+1))
      (by
        intro n hn
        exact h_nonneg n))
    simpa [hsumR.tsum_eq] using this

  -- 4) Chain the bounds
  exact h₁.trans (le_trans h₂ h₃)



/-- Product over `Fin n` of a constant equals the n-th power (for our integrand). -/
lemma prod_const_pow (x : ℝ) (n : ℕ) :
  (∏ _i : Fin n, x) = x ^ n :=
  Fin.prod_const n x

/-- Identify `S_n(J,…,J)` as the integral of the n-th power of `⟨ω,J⟩`. -/
lemma schwinger_eq_integral_pow
  (dμ : ProbabilityMeasure (FieldConfiguration 4)) (J : SchwartzTestFunction 4) (n : ℕ) :
  (SchwingerFunction dμ n (fun _ => J) : ℝ)
  = ∫ ω, (distributionPairing ω J) ^ n ∂ dμ.toMeasure := by
  -- Unfold `SchwingerFunction` and simplify the Finite product on `Fin n`
  -- to a power using `prod_const_pow`.
  classical
  unfold SchwingerFunction
  -- integrand: ∏ i, ⟨ω,J⟩ = (⟨ω,J⟩)^n
  -- Pointwise product-to-power identity
  have hω : ∀ ω : FieldConfiguration 4, (∏ _i : Fin n, distributionPairing ω J) = (distributionPairing ω J) ^ n := by
    intro ω
    simp only [prod_const_pow]
  -- Rewrite under the integral using the pointwise identity
  simp [hω]

end AQFT_exponential_series

end

/-! ## Basic Distribution Framework

The following definitions provide the foundation for viewing Schwinger functions
as distributions on product spaces. These are needed by other modules.
-/

/-- The product space of n copies of spacetime -/
abbrev SpaceTimeProduct (d n : ℕ) := (Fin n) → (SpaceTime d)

/-- Test functions on the n-fold product space -/
abbrev TestFunctionProduct (d n : ℕ) := SchwartzMap (SpaceTimeProduct d n) ℝ

end

end SchwingerDefs

/-! ### From `Schwinger/GaussianMoments.lean` -/

section SchwingerGaussianMoments

open MeasureTheory Complex Finset OSforGFF
open TopologicalSpace SchwartzMap

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

namespace GaussianMoments

open MeasureTheory Complex

/-- Auxiliary lemma: the complex pairing has an integrable square under the free GFF measure.
This is the complex analogue of `gaussian_pairing_square_integrable_real` and will serve as the
base estimate for higher Gaussian moments. -/
lemma gaussian_complex_pairing_abs_sq_integrable
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (φ : SchwartzTestFunctionℂ d) :
  Integrable (fun ω => ‖distributionPairingℂ_real ω φ‖ ^ 2)
    (gaussianFreeField_free m).toMeasure := by
  classical
  -- Split the complex test function into real and imaginary parts
  set φRe : SchwartzTestFunction d := (complex_testfunction_decompose φ).1
  set φIm : SchwartzTestFunction d := (complex_testfunction_decompose φ).2

  -- Use the proven theorem from GFFbridge (derives from gff_pairing_is_gaussian)
  have hRe_mem :
      MemLp (distributionPairingCLM φRe) (2 : ENNReal)
        (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp (m := m) (φ := φRe) (p := (2 : ENNReal)) (hp := by simp)
  have hIm_mem :
      MemLp (distributionPairingCLM φIm) (2 : ENNReal)
        (gaussianFreeField_free m).toMeasure :=
    gaussianFreeField_pairing_memLp (m := m) (φ := φIm) (p := (2 : ENNReal)) (hp := by simp)

  -- Convert the MemLp statements to integrability of the square magnitudes
  have hRe_sq : Integrable (fun ω => (distributionPairing ω φRe) ^ 2)
      (gaussianFreeField_free m).toMeasure := by
    exact hRe_mem.integrable_sq
  have hIm_sq : Integrable (fun ω => (distributionPairing ω φIm) ^ 2)
      (gaussianFreeField_free m).toMeasure := by
    exact hIm_mem.integrable_sq

  -- Assemble the complex absolute square from the real and imaginary components
  have h_pointwise :
      (fun ω => ‖distributionPairingℂ_real ω φ‖ ^ 2) =
        (fun ω => (distributionPairing ω φRe) ^ 2 + (distributionPairing ω φIm) ^ 2) := by
    funext ω
    -- Use the fact that ‖a + bi‖² = a² + b² for complex numbers
    rw [Complex.sq_norm, Complex.normSq_apply]
    -- Simplify using the definition of distributionPairingℂ_real
    simp only [distributionPairingℂ_real, φRe, φIm]
    -- Expand using the real and imaginary parts of a + I*b where a,b are real
    -- For z = a + I*b with a,b real: z.re = a, z.im = b
    -- So ‖z‖² = z.re² + z.im² = a² + b²
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    -- Simplify arithmetic: I.re = 0, I.im = 1, (real number).im = 0
    simp only [zero_mul, one_mul, mul_zero, zero_sub, zero_add]
    -- Convert back to distributionPairing and square notation
    simp only [distributionPairing, ← sq]
    -- Final simplification: a + (-0) = a
    simp only [neg_zero, add_zero]

  -- Finish by using integrability of the individual squares
  have h_sum : Integrable
      (fun ω => (distributionPairing ω φRe) ^ 2 + (distributionPairing ω φIm) ^ 2)
        (gaussianFreeField_free m).toMeasure :=
    hRe_sq.add hIm_sq
  simpa [h_pointwise]
    using h_sum

end GaussianMoments

end

end SchwingerGaussianMoments

/-! ### Moved 2026-08-30 -/

section Moved20260830

open MeasureTheory Complex QFT ProbabilityTheory OSforGFF

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-- For real test functions, the square of the Gaussian pairing is integrable under the
    free Gaussian Free Field measure. This is the diagonal (f = g) case of two-point
    integrability (from `Measure/Construct.lean`). -/
lemma gaussian_pairing_square_integrable_real
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (φ : SchwartzTestFunction d) :
  Integrable (fun ω => (distributionPairing ω φ) ^ 2)
    (gaussianFreeField_free m).toMeasure := by
  have h_memLp :=
    gaussianFreeField_pairing_memLp m φ ((2 : ℕ) : ENNReal) (by simp)
  have h_integrable_CLM := h_memLp.integrable_sq
  exact h_integrable_CLM.congr (Filter.Eventually.of_forall fun ω => rfl)

end

end Moved20260830
