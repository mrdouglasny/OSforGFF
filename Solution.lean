/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF

/-!
# Solution: the Gaussian Free Field satisfies the Osterwalder–Schrader axioms

**[SPIKE VERSION — statement under construction.]** Solution counterpart of `Challenge.lean`:
it re-declares the Challenge definitions verbatim and proves the challenge theorem from the
OSforGFF library (the dimension-generic master theorem via the canonical proper-time
propagator). This file states, in Mathlib-only terms,
the existence of the free (massive) Gaussian Free Field measure on the space of tempered
distributions over `ℝ^d` together with the Osterwalder–Schrader axioms it satisfies.

The measure is characterized uniquely by its generating functional
`Z[f] = exp (−½ ⟨f, C f⟩)`, where `C` is the free covariance `(−Δ + m²)⁻¹`, presented here by
its proper-time (heat-kernel) integral
`C(x, y) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−‖x−y‖²/(4t)} dt`.

The current spike states the characterization together with OS2 (Euclidean invariance) only.
-/

namespace Challenge

open MeasureTheory Complex

noncomputable section

/-! ## Spacetime, test functions, and field configurations -/

/-- Euclidean spacetime of dimension `d`: `ℝ^d` with the Euclidean inner-product structure. -/
abbrev SpaceTime (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Real-valued Schwartz test functions on `ℝ^d`. -/
abbrev TestFunction (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℝ

/-- Complex-valued Schwartz test functions on `ℝ^d`. -/
abbrev TestFunctionℂ (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℂ

/-- Field configurations: tempered distributions `S'(ℝ^d)`, i.e. the continuous dual of
Schwartz space equipped with the weak-* topology. -/
abbrev FieldConfiguration (d : ℕ) := WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)

/-- The cylinder σ-algebra on the weak dual of a topological vector space: the smallest
σ-algebra making every evaluation map `ω ↦ ω f` Borel-measurable. This is the standard
measurable structure for measures on distribution spaces. -/
instance measurableSpaceWeakDual {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : MeasurableSpace (WeakDual ℝ E) :=
  ⨆ (f : E), (borel ℝ).comap (fun l : WeakDual ℝ E => (l : E →L[ℝ] ℝ) f)

variable {d : ℕ}

/-! ## Pairings and generating functionals -/

/-- The pairing `⟨ω, f⟩` of a tempered distribution with a real test function. -/
def distributionPairing (ω : FieldConfiguration d) (f : TestFunction d) : ℝ := ω f

/-- The generating functional `Z[J] = ∫ e^{i⟨ω, J⟩} dμ(ω)` of a probability measure on field
configurations, evaluated on a real test function `J`. -/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (J : TestFunction d) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Postcomposition of a complex test function with an ℝ-linear continuous map `ℂ →L[ℝ] ℝ`
(such as taking real or imaginary parts), yielding a real test function. -/
def schwartz_comp_clm (f : TestFunctionℂ d) (L : ℂ →L[ℝ] ℝ) : TestFunction d :=
  SchwartzMap.mk (fun x => L (f x))
    (ContDiff.comp L.contDiff f.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := f.decay' k n
      use C * ‖L‖
      intro x
      have h_eq : (fun y => L (f y)) = L ∘ f.toFun := rfl
      have h_deriv : iteratedFDeriv ℝ n (L ∘ f.toFun) x =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x) :=
        ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt
          (WithTop.coe_le_coe.mpr le_top)
      rw [h_eq, h_deriv]
      calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
          ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
            apply mul_le_mul_of_nonneg_left
            exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
            exact pow_nonneg (norm_nonneg _) _
        _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
        _ ≤ ‖L‖ * C := by
            apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖L‖ := by ring)

/-- Decomposition of a complex test function into its real and imaginary parts, each a real
test function. -/
def complex_testfunction_decompose (f : TestFunctionℂ d) : TestFunction d × TestFunction d :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)

/-- The pairing of a (real) tempered distribution with a complex test function
`f = f_re + i f_im`, defined as `⟨ω, f⟩ = ⟨ω, f_re⟩ + i ⟨ω, f_im⟩`. -/
def distributionPairingℂ_real (ω : FieldConfiguration d) (f : TestFunctionℂ d) : ℂ :=
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- The generating functional evaluated on a complex test function:
`Z[J] = ∫ e^{i⟨ω, J⟩} dμ(ω)` with the complexified pairing. -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (J : TestFunctionℂ d) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-! ## The free covariance -/

/-- The heat-kernel radial profile in `d` dimensions:
`H_d(t, r) = (4πt)^{−d/2} · e^{−r²/(4t)}`, the Gauss kernel of `e^{tΔ}` at radius `r`. -/
def heatKernelProfile (d : ℕ) (t r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))

/-- The proper-time (Schwinger) representation of the free covariance profile:
`C_S(r) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−r²/(4t)} dt`. This is the radial kernel of
`(−Δ + m²)⁻¹` on `ℝ^d`. -/
def properTimeCovariance (d : ℕ) (m r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m ^ 2) * heatKernelProfile d t r

/-- The free covariance kernel `C(x, y)` of the massive free field: the radial proper-time
profile evaluated at `r = ‖x − y‖`. -/
def freeCovariance (d : ℕ) (m : ℝ) (x y : SpaceTime d) : ℝ :=
  properTimeCovariance d m ‖x - y‖

/-- The covariance bilinear form `⟨f, C g⟩ = ∫∫ f(x) C(x, y) g(y) dx dy` on real test
functions. -/
def covarianceForm (d : ℕ) (m : ℝ) (f g : TestFunction d) : ℝ :=
  ∫ x, ∫ y, (f x) * (freeCovariance d m x y) * (g y) ∂volume ∂volume

/-! ## The Euclidean group and its action on test functions -/

/-- Orthogonal linear isometries of `ℝ^d`: the group `O(d)`. -/
abbrev Rotation (d : ℕ) : Type :=
  LinearIsometry (RingHom.id ℝ) (SpaceTime d) (SpaceTime d)

/-- A Euclidean motion of `ℝ^d`: a rotation/reflection `R ∈ O(d)` followed by a translation,
`x ↦ R x + t`. These form the Euclidean group `E(d) = ℝ^d ⋊ O(d)`. -/
structure E (d : ℕ) where
  /-- The rotation/reflection part. -/
  R : Rotation d
  /-- The translation part. -/
  t : SpaceTime d

/-- The action of a Euclidean motion on a spacetime point: `g • x = R x + t`. -/
def act (g : E d) (x : SpaceTime d) : SpaceTime d := g.R x + g.t

/-- The inverse of a linear isometry of `ℝ^d` (finite dimension makes every isometry
surjective, so the inverse isometry exists). -/
noncomputable def Rotation.inv (g : Rotation d) : Rotation d :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

/-- The inverse Euclidean motion: `(R, t)⁻¹ = (R⁻¹, −R⁻¹ t)`. -/
noncomputable instance : Inv (E d) where
  inv g := ⟨Rotation.inv g.R, -(Rotation.inv g.R) g.t⟩

/-- The pullback map underlying the action of `g` on functions: `x ↦ g⁻¹ • x`. -/
noncomputable def euclidean_pullback (g : E d) : SpaceTime d → SpaceTime d := act g⁻¹

private lemma contDiff_act_inv (g : E d) : ContDiff ℝ ⊤ (act g⁻¹) := by
  have h₁ : ContDiff ℝ ⊤ (fun x : SpaceTime d => g⁻¹.R x) := g⁻¹.R.contDiff
  have h₂ : ContDiff ℝ ⊤ (fun _ : SpaceTime d => g⁻¹.t) := contDiff_const
  unfold act
  exact h₁.add h₂

private lemma fderiv_linear_add_const (L : SpaceTime d →L[ℝ] SpaceTime d) (c : SpaceTime d)
    (x : SpaceTime d) : fderiv ℝ (fun y => L y + c) x = fderiv ℝ L x :=
  fderiv_add_const _

private theorem fderiv_act_inv_eq_linear (g : E d) :
    (fun x => fderiv ℝ (act g⁻¹) x) = fun _ => g⁻¹.R.toContinuousLinearMap := by
  ext x v i
  let L := g⁻¹.R.toContinuousLinearMap
  calc (fderiv ℝ (act g⁻¹) x v) i
      = (fderiv ℝ (fun y => L y + g⁻¹.t) x v) i := rfl
    _ = ((fderiv ℝ (fun y => L y + g⁻¹.t) x) v) i := rfl
    _ = ((fderiv ℝ L x) v) i := by rw [fderiv_linear_add_const]
    _ = (L v) i := by rw [ContinuousLinearMap.fderiv]

private theorem fderiv_has_temperate_growth (g : E d) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x) := by
  rw [fderiv_act_inv_eq_linear g]
  exact Function.HasTemperateGrowth.const _

private theorem act_inv_poly_bound (g : E d) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : SpaceTime d, ‖act g⁻¹ x‖ ≤ C * (1 + ‖x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  have : act g⁻¹ x = g⁻¹.R x + g⁻¹.t := by simp [act]
  rw [this]
  calc ‖g⁻¹.R x + g⁻¹.t‖
      ≤ ‖g⁻¹.R x‖ + ‖g⁻¹.t‖ := norm_add_le _ _
    _ = ‖x‖ + ‖g⁻¹.t‖ := by rw [g⁻¹.R.norm_map x]
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖x‖) ^ 1 := by
        simp only [pow_one]
        ring_nf
        have h1 : 0 ≤ ‖x‖ := norm_nonneg x
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        linarith [mul_nonneg h2 h1]

/-- The pullback map `x ↦ g⁻¹ • x` has temperate growth (an affine map). -/
lemma euclidean_pullback_temperate_growth (g : E d) :
    Function.HasTemperateGrowth (euclidean_pullback g) := by
  unfold euclidean_pullback
  obtain ⟨k, C, hbound⟩ := act_inv_poly_bound g
  exact Function.HasTemperateGrowth.of_fderiv (fderiv_has_temperate_growth g)
    ((contDiff_act_inv g).differentiable WithTop.top_ne_zero) hbound

/-- The pullback map satisfies the polynomial lower bound needed to precompose Schwartz
functions: `‖x‖ ≤ C (1 + ‖g⁻¹ • x‖)^k`. -/
lemma euclidean_pullback_polynomial_bounds (g : E d) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : SpaceTime d, ‖x‖ ≤ C * (1 + ‖euclidean_pullback g x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  simp only [pow_one, euclidean_pullback, act]
  have h_iso : ‖g⁻¹.R x‖ = ‖x‖ := g⁻¹.R.norm_map x
  rw [← h_iso]
  have h_ineq : ‖g⁻¹.R x‖ ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := norm_le_add_norm_add _ _
  calc ‖g⁻¹.R x‖
      ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := h_ineq
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖g⁻¹.R x + g⁻¹.t‖) := by
        have h1 : 0 ≤ ‖g⁻¹.R x + g⁻¹.t‖ := norm_nonneg _
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        ring_nf
        linarith [mul_nonneg h2 h1]

/-- The action of a Euclidean motion on complex test functions by pullback:
`(g • f)(x) = f(g⁻¹ • x)`. -/
noncomputable def euclidean_action (g : E d) (f : TestFunctionℂ d) : TestFunctionℂ d :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f

/-! ## The Osterwalder–Schrader axioms -/

/-- **OS2 (Euclidean invariance):** the generating functional is invariant under the pullback
action of every Euclidean motion. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : E d) (f : TestFunctionℂ d),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (euclidean_action g f)

/-! ## The theorem -/

/-- **[SPIKE]** For every dimension `d ≥ 2` and mass `m > 0` there is a probability measure on
the tempered distributions `S'(ℝ^d)` — the Gaussian Free Field — whose generating functional
is the Gaussian `Z[f] = exp(−½ ⟨f, C f⟩)` with the free covariance `C = (−Δ + m²)⁻¹` in its
proper-time form, and which is invariant under the full Euclidean group. -/
theorem gaussianFreeField_exists_OS2 (d : ℕ) (hd : 2 ≤ d) (m : ℝ) (hm : 0 < m) :
    ∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      OS2_EuclideanInvariance μ := by
  haveI : Fact (2 ≤ d) := ⟨hd⟩
  haveI : Fact (0 < m) := ⟨hm⟩
  letI := OSforGFF.GFFPropagator.ofProperTime d m
  refine ⟨gaussianFreeField_free (d := d) m, fun f => ?_, ?_⟩
  · exact gff_real_characteristic (d := d) m f
  · intro g f
    exact (OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic (d := d) m).os2
      ⟨g.R, g.t⟩ f

end

end Challenge
