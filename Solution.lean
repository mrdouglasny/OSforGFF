/-
Copyright (c) 2026 Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib
import OSforGFF

/-!
# Solution: the Gaussian Free Field satisfies the Osterwalder–Schrader axioms

Solution counterpart of `Challenge.lean`: it re-declares the Challenge definitions verbatim
and proves the challenge theorem from the OSforGFF library — the witness is the library's
Minlos-constructed measure `gaussianFreeField_free` under the canonical proper-time propagator
`GFFPropagator.ofProperTime`, its characterization is `gff_real_characteristic`, and the five
OS axioms are the fields of the dimension-generic master theorem
`gaussianFreeField_satisfies_all_OS_axioms_generic`.

The Challenge (restated below) covers, in Mathlib-only terms, the construction of Euclidean
quantum field theory's
simplest interacting-free model: for every spacetime dimension `d ≥ 2` and mass `m > 0`, the
free (massive) **Gaussian Free Field** exists as a probability measure on the tempered
distributions `S'(ℝ^d)` and satisfies all five **Osterwalder–Schrader axioms** — OS0
(analyticity), OS1 (regularity), OS2 (Euclidean invariance), OS3 (reflection positivity), and
OS4 (clustering and ergodicity). By the Osterwalder–Schrader reconstruction theorem, these
axioms are precisely the conditions under which a Euclidean field theory defines a relativistic
quantum field theory satisfying the Wightman axioms.

The measure is pinned down uniquely by the characterization clause of the theorem: its
generating functional is the Gaussian `Z[f] = exp (−½ ⟨f, C f⟩)`, where `C = (−Δ + m²)⁻¹` is
the free covariance, presented here by its proper-time (heat-kernel) integral
`C(x, y) = ∫₀^∞ e^{−t m²} (4πt)^{−d/2} e^{−‖x−y‖²/(4t)} dt` — an elementary closed formula
requiring no operator theory. Without this clause the existence statement would be trivial
(the Dirac measure at `0` satisfies all five axioms); with it, the theorem asserts exactly
that *the free field* satisfies them.

All definitions below are self-contained over Mathlib: the field configuration space and its
cylinder σ-algebra, the generating functionals, the free covariance, the Euclidean group and
its action on test functions, time reflection and the Osterwalder–Schrader star operation,
positive-time test functions, time translations, the mollifier-regularized two-point function,
and the five OS axiom predicates. The theorem is proved at the end of the file.

The formulation of the axioms follows Glimm–Jaffe, *Quantum Physics: A Functional Integral
Point of View* (Springer, 1987), ch. 6, stated for probability measures on `S'(ℝ^d)`; OS3 is
the complex star formulation of Osterwalder–Schrader (*Axioms for Euclidean Green's
functions II*, Comm. Math. Phys. 42 (1975) 281–305, axiom E2).
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

/-! ## Schwinger functions and the regularized two-point function -/

/-- The `n`-point Schwinger function (correlation function) of a measure on field
configurations: `S_n(f₁, …, fₙ) = ∫ ⟨ω, f₁⟩ ⋯ ⟨ω, fₙ⟩ dμ(ω)`. -/
def SchwingerFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (n : ℕ)
    (f : Fin n → TestFunction d) : ℝ :=
  ∫ ω, (∏ i, distributionPairing ω (f i)) ∂dμ_config.toMeasure

/-- The two-point Schwinger function `S₂(f, g) = ∫ ⟨ω, f⟩ ⟨ω, g⟩ dμ(ω)`, the covariance of
the measure. -/
def SchwingerFunction₂ (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (f g : TestFunction d) : ℝ :=
  SchwingerFunction dμ_config 2 ![f, g]

lemma sub_const_hasTemperateGrowth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) : Function.HasTemperateGrowth (fun x : E => x - a) := by fun_prop

lemma sub_const_antilipschitz {E : Type*} [NormedAddCommGroup E] (a : E) :
    AntilipschitzWith 1 (fun x : E => x - a) := by
  intro x y
  simp [edist_dist, dist_eq_norm]

/-- Translation of a Schwartz function by a vector: `(translateSchwartz f a)(x) = f(x − a)`.
Translation `x ↦ x − a` is an isometry with temperate growth, so it preserves the Schwartz
class. -/
def translateSchwartz (f : TestFunction d) (a : SpaceTime d) : TestFunction d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (sub_const_hasTemperateGrowth a)
    (sub_const_antilipschitz a) f

/-- The L¹-normalized smooth bump function attached to a `ContDiffBump` centered at the
origin, viewed as a Schwartz function (it is smooth with compact support). It integrates
to `1`, so it is a mollifier. -/
def bumpToSchwartz (φ : ContDiffBump (0 : SpaceTime d)) : TestFunction d :=
  (φ.hasCompactSupport_normed (μ := volume)).toSchwartzMap φ.contDiff_normed

/-- The two-point function smeared against a mollifier: the covariance evaluated on a
normalized bump translated to `x` against the same bump at the origin,
`∫∫ φ(u − x) ⟨φ(u) φ(v)⟩ φ(v) du dv`. -/
def SmearedTwoPointFunction (dμ_config : ProbabilityMeasure (FieldConfiguration d))
    (φ : ContDiffBump (0 : SpaceTime d)) (x : SpaceTime d) : ℝ :=
  SchwingerFunction₂ dμ_config (translateSchwartz (bumpToSchwartz φ) x) (bumpToSchwartz φ)

/-- The standard mollifier sequence: bumps with outer radius `1/n` (and inner radius
`1/(2n)`), shrinking to the origin as `n → ∞`. -/
def standardBumpSequence (n : ℕ) (hn : n ≠ 0) : ContDiffBump (0 : SpaceTime d) :=
  { rIn := 1 / (2 * n)
    rOut := 1 / n
    rIn_pos := by positivity
    rIn_lt_rOut := by
      have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h2n : (0 : ℝ) < 2 * n := by positivity
      have : (2 * (n : ℝ))⁻¹ < (n : ℝ)⁻¹ := inv_strictAnti₀ hn' (by linarith)
      simp only [one_div]
      exact this }

/-- The pointwise two-point function `S₂(x)`, defined as the mollifier limit of smeared
two-point functions along the standard bump sequence, regularized to `0` at the coincident
point `x = 0` (where the two-point function of a quantum field diverges). -/
def SchwingerTwoPointFunction
    (dμ_config : ProbabilityMeasure (FieldConfiguration d)) (x : SpaceTime d) : ℝ :=
  if x = 0 then 0
  else
    Filter.limUnder Filter.atTop
      (fun n : ℕ => if hn : n = 0 then 0
        else SmearedTwoPointFunction dμ_config (standardBumpSequence n hn) x)

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
noncomputable instance instInvE : Inv (E d) where
  inv g := ⟨Rotation.inv g.R, -(Rotation.inv g.R) g.t⟩

/-- The pullback map underlying the action of `g` on functions: `x ↦ g⁻¹ • x`. -/
noncomputable def euclidean_pullback (g : E d) : SpaceTime d → SpaceTime d := act g⁻¹

lemma contDiff_act_inv (g : E d) : ContDiff ℝ ⊤ (act g⁻¹) := by
  have h₁ : ContDiff ℝ ⊤ (fun x : SpaceTime d => g⁻¹.R x) := g⁻¹.R.contDiff
  have h₂ : ContDiff ℝ ⊤ (fun _ : SpaceTime d => g⁻¹.t) := contDiff_const
  unfold act
  exact h₁.add h₂

lemma fderiv_linear_add_const (L : SpaceTime d →L[ℝ] SpaceTime d) (c : SpaceTime d)
    (x : SpaceTime d) : fderiv ℝ (fun y => L y + c) x = fderiv ℝ L x :=
  fderiv_add_const _

theorem fderiv_act_inv_eq_linear (g : E d) :
    (fun x => fderiv ℝ (act g⁻¹) x) = fun _ => g⁻¹.R.toContinuousLinearMap := by
  ext x v i
  let L := g⁻¹.R.toContinuousLinearMap
  calc (fderiv ℝ (act g⁻¹) x v) i
      = (fderiv ℝ (fun y => L y + g⁻¹.t) x v) i := rfl
    _ = ((fderiv ℝ (fun y => L y + g⁻¹.t) x) v) i := rfl
    _ = ((fderiv ℝ L x) v) i := by rw [fderiv_linear_add_const]
    _ = (L v) i := by rw [ContinuousLinearMap.fderiv]

theorem fderiv_has_temperate_growth (g : E d) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x) := by
  rw [fderiv_act_inv_eq_linear g]
  exact Function.HasTemperateGrowth.const _

theorem act_inv_poly_bound (g : E d) :
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

/-! ## Time reflection and the Osterwalder–Schrader star operation -/

/-- Dimensions admitting a time/space split are nonzero, so `(0 : Fin d)` is available. -/
instance instNeZeroOfFactTwoLe [Fact (2 ≤ d)] : NeZero d :=
  ⟨by have h : 2 ≤ d := Fact.out; omega⟩

/-- The time component `x₀` of a spacetime point (the coordinate reflected by `Θ`). -/
abbrev getTimeComponent [Fact (2 ≤ d)] (x : SpaceTime d) : ℝ :=
  x ⟨0, by have h : 2 ≤ d := Fact.out; omega⟩

/-- Time reflection `Θ : (x₀, x̄) ↦ (−x₀, x̄)`: negate the time coordinate, keep the spatial
coordinates. -/
def timeReflection [Fact (2 ≤ d)] (x : SpaceTime d) : SpaceTime d :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

/-- Time reflection as a linear map on `ℝ^d`. -/
def timeReflectionLinear [Fact (2 ≤ d)] : SpaceTime d →ₗ[ℝ] SpaceTime d :=
  { toFun := timeReflection
    map_add' := by
      intro x y
      apply PiLp.ext
      intro i
      simp only [timeReflection, WithLp.equiv_symm_apply]
      by_cases h : i = 0
      · subst h
        simp [Function.update_self]
        ring
      · simp [Function.update_of_ne h]
    map_smul' := by
      intro c x
      apply PiLp.ext
      intro i
      simp only [timeReflection, RingHom.id_apply, WithLp.equiv_symm_apply]
      by_cases h : i = 0
      · subst h
        simp [Function.update_self]
      · simp [Function.update_of_ne h] }

/-- Time reflection as a continuous linear map on `ℝ^d`. -/
noncomputable def timeReflectionCLM [Fact (2 ≤ d)] : SpaceTime d →L[ℝ] SpaceTime d :=
  timeReflectionLinear.toContinuousLinearMap (E := SpaceTime d) (F' := SpaceTime d)

open InnerProductSpace in
/-- Time reflection preserves the Euclidean inner product. -/
lemma timeReflection_inner_map [Fact (2 ≤ d)] (x y : SpaceTime d) :
    ⟪timeReflection x, timeReflection y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [inner]
  congr 1
  ext i
  simp only [timeReflection]
  by_cases h : i = 0
  · rw [h]; simp
  · simp [h]

/-- Time reflection is an involution: `Θ ∘ Θ = id`. -/
@[simp] lemma timeReflection_involutive [Fact (2 ≤ d)] (x : SpaceTime d) :
    timeReflection (timeReflection x) = x := by
  apply PiLp.ext
  intro i
  simp only [timeReflection, WithLp.equiv_symm_apply]
  by_cases h : i = 0
  · subst h
    simp [Function.update_self]
  · simp [Function.update_of_ne h]

open InnerProductSpace in
/-- Time reflection as a linear isometry equivalence of `ℝ^d`. -/
def timeReflectionLE [Fact (2 ≤ d)] : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d :=
  { toFun := timeReflection
    invFun := timeReflection
    left_inv := timeReflection_involutive
    right_inv := timeReflection_involutive
    map_add' := timeReflectionLinear.map_add'
    map_smul' := timeReflectionLinear.map_smul'
    norm_map' := by
      intro x
      show ‖timeReflection x‖ = ‖x‖
      have h : ⟪timeReflection x, timeReflection x⟫_ℝ = ⟪x, x⟫_ℝ := timeReflection_inner_map x x
      have h1 : ⟪timeReflection x, timeReflection x⟫_ℝ = ‖timeReflection x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
      have h2 : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      rw [← h1, ← h2, h] }

/-- Time reflection has temperate growth (it is a linear isometry). -/
lemma timeReflection_hasTemperateGrowth [Fact (2 ≤ d)] :
    Function.HasTemperateGrowth (timeReflection (d := d)) := by
  have h : timeReflection (d := d) = ⇑(timeReflectionCLM (d := d)) := rfl
  rw [h]
  exact ContinuousLinearMap.hasTemperateGrowth (timeReflectionCLM (d := d))

/-- Time reflection is antilipschitz (it is an isometry). -/
lemma timeReflection_antilipschitz [Fact (2 ≤ d)] :
    AntilipschitzWith 1 (timeReflection (d := d)) := by
  have h : timeReflection (d := d) = ⇑(timeReflectionLE (d := d)) := rfl
  rw [h]
  exact (timeReflectionLE (d := d)).isometry.antilipschitz

/-- Composition with time reflection, `f ↦ f ∘ Θ`, as a continuous linear map on complex
test functions. -/
noncomputable def compTimeReflection [Fact (2 ≤ d)] : TestFunctionℂ d →L[ℝ] TestFunctionℂ d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ timeReflection_hasTemperateGrowth
    timeReflection_antilipschitz

lemma starRingEnd_iteratedFDeriv_norm_eq (g : TestFunctionℂ d) (n : ℕ) (x : SpaceTime d) :
    ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (g x)) x‖ = ‖iteratedFDeriv ℝ n g x‖ := by
  have h : (fun x => starRingEnd ℂ (g x)) = Complex.conjLIE ∘ g := by
    ext y
    rw [Function.comp_apply]
    exact congr_fun (@RCLike.conjLIE_apply ℂ _) (g y)
  rw [h]
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left Complex.conjLIE g x n

/-- The Osterwalder–Schrader star operation on complex test functions: time reflection
followed by pointwise complex conjugation, `(star f)(x) = conj (f (Θ x))`. -/
noncomputable def starTestFunction [Fact (2 ≤ d)] (f : TestFunctionℂ d) : TestFunctionℂ d :=
  let f_reflected := compTimeReflection f
  ⟨fun x => starRingEnd ℂ (f_reflected x),
   by
     apply ContDiff.comp
     · exact ContinuousLinearMap.contDiff (Complex.conjLIE.toContinuousLinearMap)
     · exact f_reflected.smooth ⊤,
   fun k n => by
     obtain ⟨C, hC⟩ := f_reflected.decay' k n
     use C
     intro x
     have h_eq : ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖ =
         ‖iteratedFDeriv ℝ n f_reflected x‖ :=
       starRingEnd_iteratedFDeriv_norm_eq f_reflected n x
     calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => starRingEnd ℂ (f_reflected x)) x‖
         = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f_reflected x‖ := by rw [h_eq]
       _ ≤ C := hC x⟩

/-- The star operation as a `Star` instance on complex test functions. -/
noncomputable instance instStarTestFunction [Fact (2 ≤ d)] : Star (TestFunctionℂ d) where
  star f := starTestFunction f

/-! ## Positive-time test functions -/

/-- A spacetime point has positive time if its time component is positive. -/
def HasPositiveTime [Fact (2 ≤ d)] (x : SpaceTime d) : Prop := getTimeComponent x > 0

/-- The (open) positive-time half-space `{x : x₀ > 0}`. -/
def positiveTimeSet [Fact (2 ≤ d)] : Set (SpaceTime d) := {x | HasPositiveTime x}

/-- The ℂ-submodule of complex test functions supported in the positive-time half-space. -/
def PositiveTimeTestFunctionsℂ.submodule [Fact (2 ≤ d)] : Submodule ℂ (TestFunctionℂ d) where
  carrier := { f : TestFunctionℂ d | tsupport f ⊆ positiveTimeSet }
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    suffices h : tsupport (0 : TestFunctionℂ d) = ∅ by
      rw [h]
      apply Set.empty_subset
    rw [tsupport_eq_empty_iff]
    rfl
  add_mem' := fun {f g} hf hg => Set.Subset.trans (tsupport_add f g) (Set.union_subset hf hg)
  smul_mem' := by
    intro c f hf
    refine (tsupport_smul_subset_right (fun _ : SpaceTime d => c) f).trans hf

/-- Complex test functions supported at positive time (the domain of the OS3 reflection
positivity form). -/
abbrev PositiveTimeTestFunctionℂ (d : ℕ) [Fact (2 ≤ d)] : Type :=
  PositiveTimeTestFunctionsℂ.submodule (d := d)

/-! ## Time translations -/

/-- Time translation on spacetime points: shift the time coordinate by `s`, keep the spatial
coordinates: `(timeShift s u)₀ = u₀ + s` and `(timeShift s u)ᵢ = uᵢ` for `i ≠ 0`. -/
def timeShift (s : ℝ) (u : SpaceTime d) : SpaceTime d :=
  WithLp.toLp 2 (fun i => if i.val = 0 then u.ofLp i + s else u.ofLp i)

/-- Time shift preserves the Euclidean distance. -/
lemma timeShift_dist (s : ℝ) (u v : SpaceTime d) :
    dist (timeShift s u) (timeShift s v) = dist u v := by
  simp only [EuclideanSpace.dist_eq, timeShift]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · congr 1; simp only [Real.dist_eq, add_sub_add_right_eq_sub]
  · rfl

/-- Time shift is an isometry of `ℝ^d`. -/
lemma timeShift_isometry (s : ℝ) : Isometry (timeShift (d := d) s) := by
  rw [isometry_iff_dist_eq]
  exact fun u v => timeShift_dist s u v

lemma timeShift_antilipschitz (s : ℝ) : AntilipschitzWith 1 (timeShift (d := d) s) :=
  (timeShift_isometry s).antilipschitz

/-- The constant vector expressing `timeShift` as `id + const`. -/
def timeShiftConst (s : ℝ) : SpaceTime d :=
  WithLp.toLp 2 (fun i => if i.val = 0 then s else 0)

lemma timeShift_eq_add_const (s : ℝ) (u : SpaceTime d) :
    timeShift s u = u + timeShiftConst s := by
  simp only [timeShift, timeShiftConst]
  ext i
  simp only [PiLp.add_apply]
  split_ifs with h <;> ring

/-- Time shift has temperate growth (it is an affine map). -/
lemma timeShift_hasTemperateGrowth (s : ℝ) :
    Function.HasTemperateGrowth (timeShift (d := d) s) := by
  have h_fderiv_temperate : Function.HasTemperateGrowth (fderiv ℝ (timeShift (d := d) s)) := by
    have h_eq : fderiv ℝ (timeShift (d := d) s) =
        fun _ => ContinuousLinearMap.id ℝ (SpaceTime d) := by
      ext x v
      have h : timeShift (d := d) s = fun u => u + timeShiftConst s :=
        funext (timeShift_eq_add_const s)
      rw [h]
      simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply]
    rw [h_eq]
    exact Function.HasTemperateGrowth.const _
  have h_diff : Differentiable ℝ (timeShift (d := d) s) := by
    intro x
    have h : timeShift (d := d) s = fun u => u + timeShiftConst s :=
      funext (timeShift_eq_add_const s)
    rw [h]
    exact differentiableAt_id.add_const _
  have h_bound : ∀ x : SpaceTime d,
      ‖timeShift s x‖ ≤ (1 + ‖timeShiftConst (d := d) s‖) * (1 + ‖x‖) ^ 1 := by
    intro x
    rw [timeShift_eq_add_const, pow_one]
    calc ‖x + timeShiftConst s‖
        ≤ ‖x‖ + ‖timeShiftConst s‖ := norm_add_le _ _
      _ ≤ (1 + ‖timeShiftConst s‖) * (1 + ‖x‖) := by
          nlinarith [norm_nonneg x, norm_nonneg (timeShiftConst (d := d) s)]
  exact Function.HasTemperateGrowth.of_fderiv h_fderiv_temperate h_diff h_bound

/-- Time translation `f ↦ f ∘ (timeShift s)` as a continuous linear map on real test
functions: `(T_s f)(t, x̄) = f(t + s, x̄)`. -/
def timeTranslationSchwartzCLM (s : ℝ) : TestFunction d →L[ℝ] TestFunction d :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (timeShift_hasTemperateGrowth s)
    (timeShift_antilipschitz s)

/-- Time translation on tempered distributions, by duality:
`⟨T_s ω, f⟩ = ⟨ω, T_{−s} f⟩`. -/
def timeTranslationDistribution (s : ℝ) (ω : FieldConfiguration d) : FieldConfiguration d :=
  ω.comp (timeTranslationSchwartzCLM (-s))

/-! ## The Osterwalder–Schrader axioms -/

/-- **OS0 (Analyticity):** the generating functional is entire in the complex smearing
parameters: for every finite family `J₁, …, Jₙ` of complex test functions, the map
`z ↦ Z[∑ᵢ zᵢ Jᵢ]` is analytic on all of `ℂⁿ`. -/
def OS0_Analyticity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (J : Fin n → TestFunctionℂ d),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      GJGeneratingFunctionalℂ dμ_config (∑ i, z i • J i)) Set.univ

/-- Local integrability of the pointwise two-point function, the additional condition OS1
imposes in the borderline case `p = 2`. -/
def TwoPointIntegrable (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  LocallyIntegrable (fun x => SchwingerTwoPointFunction dμ_config x) volume

/-- **OS1 (Regularity):** the generating functional satisfies an exponential bound
`‖Z[f]‖ ≤ exp (c (‖f‖₁ + ‖f‖ₚᵖ))` for some `1 ≤ p ≤ 2` and `c > 0`; when `p = 2`, the
two-point function is additionally required to be locally integrable. -/
def OS1_Regularity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : TestFunctionℂ d),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)

/-- **OS2 (Euclidean invariance):** the generating functional is invariant under the pullback
action of every Euclidean motion. -/
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : E d) (f : TestFunctionℂ d),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (euclidean_action g f)

/-- **OS3 (Reflection positivity):** the generating functional defines a positive
semi-definite Hermitian form on test functions supported at positive time. This is the
complex (star) formulation of Osterwalder–Schrader (1975, axiom E2): for all positive-time
complex test functions `f₁, …, fₙ` and coefficients `c₁, …, cₙ ∈ ℂ`,
`∑ᵢⱼ c̄ᵢ cⱼ Z[fᵢ − fⱼ*] ≥ 0`, where `(f*)(x) = conj (f (Θ x))` combines time reflection
with complex conjugation. -/
def OS3_ReflectionPositivity [Fact (2 ≤ d)]
    (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunctionℂ d) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config
        ((f i).val - star ((f j).val))).re

/-- **OS4 (Clustering):** correlations of distant regions decay:
`Z[f + T_a g] → Z[f] Z[g]` as the translation `‖a‖ → ∞`, so that widely separated test
functions become statistically independent. -/
def OS4_Clustering (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (f g : TestFunction d) (ε : ℝ), ε > 0 → ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime d),
    ‖a‖ > R →
    ‖GJGeneratingFunctional dμ_config (f + translateSchwartz g a) -
     GJGeneratingFunctional dμ_config f * GJGeneratingFunctional dμ_config g‖ < ε

/-- **OS4 (Ergodicity):** for observables `A(ω) = ∑ⱼ zⱼ e^{⟨ω, fⱼ⟩}`, the time average
`(1/T) ∫₀ᵀ A(T_s ω) ds` converges to the expectation `𝔼_μ[A]` in `L²(μ)` as `T → ∞`. -/
def OS4_Ergodicity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → TestFunctionℂ d),
    let μ := dμ_config.toMeasure
    let A : FieldConfiguration d → ℂ := fun ω =>
      ∑ j, z j * Complex.exp (distributionPairingℂ_real ω (f j))
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ ω, ‖(1 / T) * ∫ s in Set.Icc (0 : ℝ) T,
          A (timeTranslationDistribution s ω)
          - ∫ ω', A ω' ∂μ‖ ^ 2 ∂μ)
      Filter.atTop
      (nhds 0)

/-! ## The theorem -/

/-- **The Gaussian Free Field satisfies the Osterwalder–Schrader axioms, in every dimension
`d ≥ 2`.** For every mass `m > 0` there is a probability measure `μ` on the tempered
distributions `S'(ℝ^d)` — the free (massive) Gaussian Free Field — such that:

* `μ` is uniquely characterized by its generating functional
  `Z[f] = exp (−½ ⟨f, C f⟩)`, where `C = (−Δ + m²)⁻¹` is the free covariance in its
  proper-time form (this clause pins `μ` down: a Gaussian measure is determined by its
  characteristic functional); and
* `μ` satisfies the five Osterwalder–Schrader axioms: OS0 (analyticity), OS1 (regularity),
  OS2 (Euclidean invariance), OS3 (reflection positivity, complex star formulation), and
  OS4 (both clustering and ergodicity).

The dimension hypothesis `2 ≤ d` enters through the time/space split used by OS3 and is
carried as a `Fact` instance so the positive-time apparatus can consume it. -/
theorem gaussianFreeField_satisfies_OS_axioms (d : ℕ) [Fact (2 ≤ d)] (m : ℝ) (hm : 0 < m) :
    ∃ μ : ProbabilityMeasure (FieldConfiguration d),
      (∀ f : TestFunction d,
        GJGeneratingFunctional μ f =
          Complex.exp (-(1 / 2 : ℂ) * ((covarianceForm d m f f : ℝ) : ℂ))) ∧
      OS0_Analyticity μ ∧ OS1_Regularity μ ∧ OS2_EuclideanInvariance μ ∧
      OS3_ReflectionPositivity μ ∧ OS4_Clustering μ ∧ OS4_Ergodicity μ := by
  haveI : Fact (0 < m) := ⟨hm⟩
  letI := OSforGFF.GFFPropagator.ofProperTime d m
  have master := OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic (d := d) m
  refine ⟨gaussianFreeField_free (d := d) m,
    fun f => gff_real_characteristic (d := d) m f,
    master.os0, master.os1,
    fun g f => master.os2 ⟨g.R, g.t⟩ f,
    fun n f c => master.os3 n (fun i => ⟨(f i).val, (f i).property⟩) c,
    master.os4_clustering, master.os4_ergodicity⟩

end

end Challenge
