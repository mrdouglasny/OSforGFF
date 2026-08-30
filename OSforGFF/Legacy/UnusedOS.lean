/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.OS.OS0_Analyticity
import OSforGFF.OS.OS1_Regularity
import OSforGFF.OS.OS3_MixedRep
import OSforGFF.OS.OS3_ReflectionPositivity
import OSforGFF.OS.OS4_Clustering
import OSforGFF.Covariance.Propagator

/-!
# LEGACY — unused OS-layer and covariance-layer declarations (off the build graph)

**Status: legacy.** Proven declarations from the OS-axiom and covariance layers that no
declaration on the build graph consumes. Preserved here with full proofs; **not on the root
import graph**. Verify in isolation with

    lake env lean OSforGFF/Legacy/UnusedOS.lean

Former `private` markers are dropped for archival visibility. Declarations keep their
original namespaces; each block re-declares the `open`/`variable` context of its source file.
Two tiny helpers are DUPLICATED rather than moved: `QFT.IsRePSD` and
`QFT.quadForm_eq_double_sum` remain `private` in `OS/OS3_ReflectionPositivity.lean` (live
lemmas there still use them), so this file carries its own copies for the moved
`isRePSD_of_posSemidef`.

## Supersession map

From `OS/OS0_Analyticity.lean` (side lemmas of the holomorphic-integral OS0 proof; the live
chain uses the measurable/integrable siblings that remain on-graph):
- `QFT.distributionPairingℂ_real_continuous` — continuity in ω; the OS0 proof only needs
  measurability (`distributionPairingℂ_real_measurable`).
- `QFT.gff_integrand_measurable`, `QFT.gff_integrand_norm_integrable` (moved 2026-08-30) —
  packaged measurability/integrability of the generating-functional integrand; the OS0
  proof derives both inline from `distributionPairingℂ_real_measurable` and
  `gff_exp_neg_pairing_integrable`.
- `QFT.gff_integrand_analytic` — analyticity of the integrand at a point; the proof works
  through `gff_cf_slice_entire` and the dominated-derivative machinery instead.
- `QFT.gff_exp_abs_sum_memLp` — L² bound for finite products of exponentials of pairings.
- `QFT.gff_integrand_integrable` — integrability of the generating-functional integrand.

From `OS/OS1_Regularity.lean`:
- `schwingerTwoPoint_measurable` — a.e. strong measurability of the abstract two-point
  function; the OS1 proof uses `schwingerTwoPoint_ae_eq_kernel` and kernel integrability
  directly.

From `OS/OS3_MixedRep.lean` (steps of the pre-H3 OS3 chain, superseded by the order-`d`
mixed-representation route through `OS3_MixedRepInfra`):
- `normalization_constant_laplace` — a normalization identity with the dimension hard-coded
  to `d = 4` (statement in powers `4`/`3`), from the original 4D development.
- `mixed_rep_to_k0_inside_integrand` — the Lorentzian Fourier-inversion step; consumed only
  by `bilinear_to_k0_inside` (moved with it).
- `bilinear_to_k0_inside` — the Bessel-form-to-k₀-inside-momentum-form conversion; a large
  OS3 chain step off the current proof path.

From `OS/OS3_ReflectionPositivity.lean`:
- `QFT.isRePSD_of_posSemidef` (formerly `private`) — the unused direction of the
  `IsRePSD`/`Matrix.PosSemidef` bridge (the proof uses `posSemidef_of_isRePSD_isHermitian`).

From `OS/OS4_Clustering.lean` (the alternative ε–δ clustering formulation; the OS4 proof
path goes through `OS4_PolynomialClustering`):
- `QFT.CovarianceClustering_real`, `QFT.freeCovarianceClustering_real` — a closed pair:
  the qualitative clustering predicate and its GFF instance (its only consumer).

From `Covariance/Propagator.lean`:
- `freeCovariance_isometry_invariant` — isometry invariance of the position kernel; OS2
  invariance is proven from `freeCovariance_euclidean_invariant`
  (`Covariance/ParsevalGeneric.lean`), not from this lemma.
-/

/-! ### From `OS/OS0_Analyticity.lean` -/

section OS0Analyticity

open MeasureTheory Complex BigOperators SchwartzMap OSforGFF
open scoped MeasureTheory ComplexConjugate

noncomputable section

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]
variable (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]

omit [Fact (2 ≤ d)] in
/-- The complex pairing is continuous in ω.
    This follows from the continuity of the evaluation map on WeakDual. -/
theorem distributionPairingℂ_real_continuous (f : SchwartzTestFunctionℂ d) :
    Continuous (fun ω : FieldConfiguration d => distributionPairingℂ_real ω f) := by
  -- distributionPairingℂ_real ω f = ω f_re + I * ω f_im
  -- where f_re = schwartz_comp_clm f reCLM and f_im = schwartz_comp_clm f imCLM
  simp only [distributionPairingℂ_real, complex_testfunction_decompose]
  -- Now we need: Continuous (ω ↦ ↑(ω (schwartz_comp_clm f reCLM)) + I * ↑(ω (schwartz_comp_clm f imCLM)))
  -- Each evaluation ω ↦ ω g is continuous by WeakDual.eval_continuous
  have h_re : Continuous (fun ω : FieldConfiguration d => (ω (schwartz_comp_clm f Complex.reCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  have h_im : Continuous (fun ω : FieldConfiguration d => (ω (schwartz_comp_clm f Complex.imCLM) : ℂ)) :=
    Complex.continuous_ofReal.comp (WeakDual.eval_continuous _)
  -- The full pairing is a continuous combination
  exact h_re.add (continuous_const.mul h_im)

omit [Fact (2 ≤ d)] in
/-- The GFF integrand is analytic in z for each fixed field configuration ω.
    This follows from the fact that:
    1. z ↦ ∑ᵢ zᵢ • Jᵢ is linear (hence analytic) in z
    2. ω ↦ ⟨ω, f⟩ is linear in f
    3. exp(i · _) is entire -/
theorem gff_integrand_analytic
    (n : ℕ) (J : Fin n → SchwartzTestFunctionℂ d) (ω : FieldConfiguration d) (z₀ : Fin n → ℂ) :
    AnalyticAt ℂ
      (fun z : Fin n → ℂ =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      z₀ := by
  -- The function is exp ∘ (I * pairing ∘ linear_combination)
  -- Each component is analytic, and composition of analytic functions is analytic
  -- exp is entire, so we need to show the argument is analytic
  apply AnalyticAt.cexp
  -- Now show I * distributionPairingℂ_real ω (∑ i, z i • J i) is analytic in z
  apply AnalyticAt.mul
  · -- Complex.I is constant, hence analytic
    exact analyticAt_const
  · -- distributionPairingℂ_real ω (∑ i, z i • J i) is analytic in z
    -- The function z ↦ distributionPairingℂ_real ω (∑ i, z i • J i) is linear in z
    -- because distributionPairingℂ_real is linear in its test function argument
    -- and the sum is linear in z.

    -- A linear function from a finite-dimensional space to ℂ is analytic.
    -- The function is: z ↦ ∑ i, z i * (distributionPairingℂ_real ω (J i))
    -- which is a finite sum of z i times constants.

    -- Rewrite using linearity of distributionPairingℂ_real
    have h_linear : ∀ z : Fin n → ℂ, distributionPairingℂ_real ω (∑ i, z i • J i) =
        ∑ i, z i * distributionPairingℂ_real ω (J i) := fun z => by
      -- distributionPairingℂ_real is linear in the test function
      -- Use pairing_linear_combo: pairing(t•f + s•g) = t * pairing(f) + s * pairing(g)
      -- First establish the basic linearity properties
      have h_add : ∀ f g : SchwartzTestFunctionℂ d, distributionPairingℂ_real ω (f + g) =
          distributionPairingℂ_real ω f + distributionPairingℂ_real ω g := fun f g => by
        have := pairing_linear_combo ω f g 1 1
        simp at this
        exact this
      have h_smul : ∀ (c : ℂ) (f : SchwartzTestFunctionℂ d), distributionPairingℂ_real ω (c • f) =
          c * distributionPairingℂ_real ω f := fun c f => by
        have := pairing_linear_combo ω f 0 c 0
        simp at this
        exact this
      have h_zero : distributionPairingℂ_real ω 0 = 0 := by
        have := pairing_linear_combo ω 0 0 0 0
        simp at this
        exact this
      -- Use Finset.induction_on for the sum
      have h_gen : ∀ (s : Finset (Fin n)),
          distributionPairingℂ_real ω (∑ i ∈ s, z i • J i) =
          ∑ i ∈ s, z i * distributionPairingℂ_real ω (J i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp [h_zero]
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          rw [h_add, h_smul, ih]
      exact h_gen Finset.univ
    -- Now show ∑ i, z i * c_i is analytic (it's a polynomial)
    simp_rw [h_linear]
    -- Use Finset.analyticAt_fun_sum: if each f_i is analytic, then z ↦ ∑ i, f_i z is analytic
    apply Finset.analyticAt_fun_sum
    intro i _
    -- Show z ↦ z i * c_i is analytic
    apply AnalyticAt.mul
    · -- z ↦ z i is a continuous linear map (projection), hence analytic
      exact ContinuousLinearMap.analyticAt (ContinuousLinearMap.proj (R := ℂ) i) z₀
    · -- c_i = distributionPairingℂ_real ω (J i) is a constant function in z
      exact analyticAt_const

/-- Product of exponentials of absolute pairings is in L².
    If we have k test functions g₁, ..., gₖ, then exp(∑ᵢ |ω gᵢ|) = ∏ᵢ exp(|ω gᵢ|).
    Each exp(|ω gᵢ|) ∈ L^(2k) by gff_exp_abs_pairing_memLp.
    By generalized Hölder (MemLp.prod'), a product of k functions in L^(2k) is in L². -/
lemma gff_exp_abs_sum_memLp {ι : Type*} (s : Finset ι) (g : ι → SchwartzTestFunction d) :
    MemLp (fun ω : FieldConfiguration d => Real.exp (∑ i ∈ s, |ω (g i)|)) 2 (gaussianFreeField_free (d := d) m).toMeasure := by
  -- Rewrite exp(sum) as product of exp
  have h_eq : (fun ω : FieldConfiguration d => Real.exp (∑ i ∈ s, |ω (g i)|)) =
              (fun ω : FieldConfiguration d => ∏ i ∈ s, Real.exp |ω (g i)|) := by
    ext ω; exact Real.exp_sum s (fun i => |ω (g i)|)
  rw [h_eq]
  -- Handle empty case
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [memLp_const]
  -- For nonempty s, use MemLp.prod' with p i = 2 * s.card for each i
  let k : ℕ := s.card
  have hk_pos : 0 < k := Finset.card_pos.mpr hs
  -- Each factor is in L^(2k)
  have h_each : ∀ i ∈ s, MemLp (fun ω : FieldConfiguration d => Real.exp |ω (g i)|)
      (2 * k : ℕ) (gaussianFreeField_free (d := d) m).toMeasure := by
    intro i _
    exact gff_exp_abs_pairing_memLp m (g i) (2 * k : ℕ) (ENNReal.natCast_ne_top _)
  -- Apply MemLp.prod' with constant exponent 2k for each factor
  have h_prod := MemLp.prod' (s := s) (p := fun _ => (2 * k : ℕ))
    (f := fun i (ω : FieldConfiguration d) => Real.exp |ω (g i)|)
    (fun i hi => h_each i hi)
  -- The resulting exponent is (∑ i ∈ s, 1/(2k))⁻¹ = (k/(2k))⁻¹ = 2
  convert h_prod using 1
  -- Goal: 2 = (∑ i ∈ s, ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Goal: 2 = (s.card * ((2 * k : ℕ) : ENNReal)⁻¹)⁻¹
  -- Since k = s.card, this is (k * (2k)⁻¹)⁻¹ = (1/2)⁻¹ = 2
  have hk_ne_zero : (s.card : ENNReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk_pos.ne'
  have hk_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top s.card
  -- Rewrite (2 * k : ℕ) as 2 * s.card in ENNReal using k = s.card
  simp only [k]
  have h_cast : ((2 * s.card : ℕ) : ENNReal) = 2 * s.card := by norm_cast
  rw [h_cast]
  -- Goal: 2 = (s.card * (2 * s.card)⁻¹)⁻¹
  -- Strategy: s.card * (2 * s.card)⁻¹ = s.card / (2 * s.card) = 1/2, so inverse is 2
  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  -- First simplify (2 * s.card)⁻¹ = 2⁻¹ * s.card⁻¹
  rw [ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)]
  -- Goal: 2 = (s.card * (2⁻¹ * s.card⁻¹))⁻¹
  rw [mul_comm (2 : ENNReal)⁻¹ (s.card : ENNReal)⁻¹]
  rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hk_ne_zero hk_ne_top]
  -- Goal: 2 = (1 * 2⁻¹)⁻¹
  rw [one_mul]
  -- Goal: 2 = 2⁻¹⁻¹
  simp only [inv_inv]

/-- The GFF integrand for the generating functional is measurable in ω for each z
    (from `OS/OS0_Analyticity.lean`, moved 2026-08-30). -/
theorem gff_integrand_measurable
    (n : ℕ) (J : Fin n → SchwartzTestFunctionℂ d) (z : Fin n → ℂ) :
    AEStronglyMeasurable
      (fun ω : FieldConfiguration d =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (gaussianFreeField_free (d := d) m).toMeasure := by
  exact (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (distributionPairingℂ_real_measurable _))).aestronglyMeasurable

/-- The integral of ‖exp(I * distributionPairingℂ_real ω f)‖ is finite for any complex test
    function (from `OS/OS0_Analyticity.lean`, moved 2026-08-30). -/
lemma gff_integrand_norm_integrable (f : SchwartzTestFunctionℂ d) :
    Integrable (fun ω : FieldConfiguration d =>
        ‖Complex.exp (Complex.I * distributionPairingℂ_real ω f)‖)
      (gaussianFreeField_free (d := d) m).toMeasure := by
  simp_rw [norm_exp_I_distributionPairingℂ_real]
  exact gff_exp_neg_pairing_integrable m (complex_testfunction_decompose f).2

/-- The GFF integrand is integrable for each z.
    This follows from the norm being exp(-(ω f_im)) which is integrable by
    Gaussian exponential integrability. -/
theorem gff_integrand_integrable (n : ℕ) (J : Fin n → SchwartzTestFunctionℂ d) (z : Fin n → ℂ) :
    Integrable
      (fun ω : FieldConfiguration d =>
        Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (gaussianFreeField_free (d := d) m).toMeasure := by
  -- The norm is exp(-(ω f_im)) which is integrable
  have h_norm := gff_integrand_norm_integrable m (∑ i, z i • J i)
  -- Use Integrable.of_norm - h_norm is already an Integrable statement
  -- We need to convert from norm integrable to integrable
  have h_meas : AEStronglyMeasurable
      (fun ω => Complex.exp (Complex.I * distributionPairingℂ_real ω (∑ i, z i • J i)))
      (gaussianFreeField_free (d := d) m).toMeasure := gff_integrand_measurable m n J z
  exact (integrable_norm_iff h_meas).mp h_norm

end QFT

end

end OS0Analyticity

/-! ### From `OS/OS1_Regularity.lean` -/

section OS1Regularity

open MeasureTheory Complex BigOperators SchwartzMap Real QFT OSforGFF
open scoped MeasureTheory ENNReal

variable {d : ℕ} [Fact (2 ≤ d)]

/-- The abstract two-point Schwinger function of the GFF is a.e. strongly measurable. -/
theorem schwingerTwoPoint_measurable (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    AEStronglyMeasurable
      (fun x => SchwingerTwoPointFunction (gaussianFreeField_free (d := d) m) x)
      volume :=
  (freeCovarianceKernel_integrable (d := d) (m := m)).aestronglyMeasurable.congr
    (schwingerTwoPoint_ae_eq_kernel m).symm

end OS1Regularity

/-! ### From `OS/OS3_MixedRep.lean` -/

section OS3MixedRep

open MeasureTheory Complex Real Filter QFT LaplaceIntegral OSforGFF
open TopologicalSpace
open scoped Real InnerProductSpace BigOperators

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)] {m : ℝ} [Fact (0 < m)]

/-- The normalization constant relation:
    (1/(2π)^d) × π = 1/(2(2π)^{d−1})

    Proof: (2π)^d = 2 × (2π)^{d−1} × π, so π/(2π)^d = 1/(2(2π)^{d−1}) -/
lemma normalization_constant_laplace :
    (1 / (2 * π) ^ 4 : ℝ) * π = 1 / (2 * (2 * π) ^ 3) := by field_simp

omit [Fact (2 ≤ d)] in
/-- The mixed representation integrand can be converted to the k₀-inside form
    using the Fourier inversion identity for the Lorentzian.

    By `fourier_lorentzian_1d_neg`:
    (π/ω) exp(-ω|t|) = ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀

    So: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²) dk₀ -/
lemma mixed_rep_to_k0_inside_integrand (k_spatial : (SpatialCoords d)) (m : ℝ) [Fact (0 < m)]
    (t : ℝ) :
    let ω := Real.sqrt (‖k_spatial‖^2 + m^2)
    ((1 / ω : ℝ) : ℂ) * Complex.exp (-(|t| : ℝ) * ω) =
    (1 / π : ℝ) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) := by
  intro ω
  have hω_pos : 0 < ω := by
    simp only [ω]
    apply Real.sqrt_pos_of_pos
    have hm : 0 < m := Fact.out
    nlinarith [sq_nonneg ‖k_spatial‖]
  -- By fourier_lorentzian_1d_neg: ∫ exp(-ik₀t)/(k₀²+ω²) = (π/ω) exp(-ω|t|)
  have h_fourier := fourier_lorentzian_1d_neg ω hω_pos t
  -- Rearrange: (1/ω) exp(-ω|t|) = (1/π) * (π/ω) exp(-ω|t|) = (1/π) * ∫...
  rw [h_fourier]
  push_cast
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hω_ne : ω ≠ 0 := ne_of_gt hω_pos
  field_simp

/-- **Bessel covariance bilinear form equals the k₀-inside momentum form.**

    This follows from:
    1. `bessel_bilinear_eq_mixed_representation`: Bessel = mixed rep
    2. `mixed_rep_to_k0_inside_integrand`: mixed rep integrand = k₀-inside integrand

    The conversion between normalizations works out because:
    - Mixed rep has factor: 1/(2(2π)^{d-1})
    - Converting (1/ω) to (1/π)∫... multiplies by (1/π)
    - Combined: 1/(2π(2π)^{d-1}) = 1/(2π)^d ✓

    **Proof sketch**:
    1. Apply `bessel_bilinear_eq_mixed_representation` to convert LHS to mixed rep
    2. Use `mixed_rep_to_k0_inside_integrand`: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀}...
    3. Factor the spatial phase into the k₀ integral
    4. Combine normalizations: 1/(2(2π)^{d-1}) × (1/π) = 1/(2π)^d -/
theorem bilinear_to_k0_inside (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : (SchwartzTestFunctionℂ d))
    (hf_supp : ∀ x, x 0 ≤ 0 → f x = 0) :
  ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
    (starRingEnd ℂ (f x)) *
    (freeCovariance d m (timeReflection x) y : ℂ) *
    f y =
  (1 / (2 * π) ^ d : ℝ) *
  ∫ k_spatial : (SpatialCoords d), ∫ x : (SpaceTime d), ∫ y : (SpaceTime d),
    (starRingEnd ℂ (f x)) * f y *
    (∫ k0 : ℝ, Complex.exp (-Complex.I * (k0 * (-(x 0) - y 0) +
      spatialDot k_spatial (spatialPart x - spatialPart y))) /
        (k0^2 + (Real.sqrt (‖k_spatial‖^2 + m^2))^2)) := by
  -- Step 1: Convert LHS to mixed representation
  rw [bessel_bilinear_eq_mixed_representation m f hf_supp]
  -- Now LHS = (1/(2(2π)^{d-1})) * ∫_{k_sp} ∫_x ∫_y f̄ f (1/ω) exp(-ω|t|) exp(-i k·r)
  -- RHS = (1/(2π)^d) * ∫_{k_sp} ∫_x ∫_y f̄ f [∫_{k₀} exp(-iφ)/(k₀²+ω²)]

  -- Step 2: Prove normalization identity (as complex numbers)
  have h_norm : ((1 / (2 * (2 * π) ^ (d - 1)) : ℝ) : ℂ) =
      ((1 / (2 * π) ^ d : ℝ) : ℂ) * (π : ℂ) := by
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have h2π : (2 * (π : ℂ)) ≠ 0 := by simp [hπ]
    have hd1 : d - 1 + 1 = d := by have h : 2 ≤ d := Fact.out; omega
    have hpow : (2 * (π : ℂ)) ^ d = (2 * (π : ℂ)) ^ (d - 1) * (2 * (π : ℂ)) := by
      conv_lhs => rw [← hd1]
      rw [pow_succ]
    push_cast
    rw [hpow]
    field_simp

  -- Step 3: Rewrite coefficient using h_norm and rearrange to match RHS structure
  conv_lhs => rw [h_norm]
  -- Now LHS = ((1/(2π)^d) * π) * ∫...
  -- RHS = (1/(2π)^d) * ∫...
  -- Rearrange LHS to (1/(2π)^d) * (π * ∫...)
  rw [mul_comm (((1 / (2 * π) ^ d : ℝ) : ℂ)) ((π : ℂ))]
  -- Now LHS = (π * (1/(2π)^d)) * ∫...
  rw [mul_assoc]
  -- Now LHS = π * ((1/(2π)^d) * ∫...)
  rw [← mul_assoc ((π : ℂ)) _ _]
  rw [mul_comm ((π : ℂ)) (((1 / (2 * π) ^ d : ℝ) : ℂ))]
  rw [mul_assoc]
  -- Now LHS = (1/(2π)^d) * (π * ∫...)

  -- Step 4: Show the integrals are equal
  congr 1
  -- Need to show: π * ∫_{k_sp} ... (mixed rep integrand) = ∫_{k_sp} ... (k₀-inside integrand)
  -- Pull π into the integral
  have h_icm_sc : ∀ (c : ℂ) (g : (SpatialCoords d) → ℂ),
      c * ∫ a, g a = ∫ a, c * g a :=
    fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
  have h_icm_st : ∀ (c : ℂ) (g : (SpaceTime d) → ℂ),
      c * ∫ a, g a = ∫ a, c * g a :=
    fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
  rw [h_icm_sc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with k_spatial
  -- For each k_spatial, show the inner integrals are equal
  rw [h_icm_st]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [h_icm_st]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y

  -- Now at the pointwise level:
  -- LHS: π * (f̄ f (1/ω) exp(-ω|t|) exp(-i k·r))
  -- RHS: f̄ f [∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²)]
  set ω := Real.sqrt (‖k_spatial‖^2 + m^2) with hω_def
  set t := -(x 0) - y 0 with ht_def
  set r_spatial := spatialPart x - spatialPart y with hr_def

  -- Use the key identity: (1/ω) exp(-ω|t|) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)
  have h_key := mixed_rep_to_k0_inside_integrand k_spatial m t
  simp only at h_key

  -- Factor the spatial phase into the k₀ integral
  have h_phase_factor : ∀ k0 : ℝ,
      Complex.exp (-Complex.I * (k0 * t + spatialDot k_spatial r_spatial)) =
      Complex.exp (-Complex.I * k0 * t) * Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by
    intro k0
    rw [← Complex.exp_add]
    congr 1
    ring

  -- Factor spatial phase out of the k₀ integral
  have h_integral_factor :
      ∫ k0 : ℝ, Complex.exp (-Complex.I * (k0 * t + spatialDot k_spatial r_spatial)) /
        (k0^2 + ω^2) =
      (Complex.exp (-Complex.I * spatialDot k_spatial r_spatial)) *
      ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) := by
    have h_icm : ∀ (c : ℂ) (g : ℝ → ℂ),
        c * ∫ a, g a = ∫ a, c * g a :=
      fun c g => (MeasureTheory.integral_const_mul (L := ℂ) c g).symm
    rw [h_icm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with k0
    rw [h_phase_factor]
    ring

  -- The goal is now at the pointwise level:
  -- LHS: π * (f̄ f (1/ω) exp(-|t|ω) exp(-i k·r))
  -- RHS: f̄ f [∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²)]

  -- h_integral_factor says:
  -- ∫_{k₀} exp(-i(k₀t + k·r))/(k₀²+ω²) = exp(-i k·r) * ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)

  -- h_key says: (1/ω) exp(-|t|ω) = (1/π) ∫_{k₀} exp(-ik₀t)/(k₀²+ω²)

  -- First, convert the RHS to use t instead of the explicit expression
  have ht_eq : (-↑(x.ofLp 0) - ↑(y.ofLp 0) : ℂ) = (t : ℂ) := by
    simp only [ht_def]
    push_cast
    ring

  -- Rewrite the RHS to use t
  conv_rhs => rw [ht_eq]

  -- Substitute RHS using h_integral_factor
  rw [h_integral_factor]

  -- Now RHS = f̄ f (exp(-i k·r) * ∫_{k₀} exp(-ik₀t)/(k₀²+ω²))

  -- Simplify LHS using h_key
  simp only [hω_def] at h_key ⊢

  -- LHS: π * (f̄ f (1/ω) exp(-|t|ω) exp(-i k·r))
  -- Use h_key: (1/ω) exp(-|t|ω) = (1/π) ∫_{k₀}...

  -- First, simplify π * (1/π) = 1
  have hπ_ne : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h_pi_cancel : ((π : ℝ) : ℂ) * ((1 / π : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp

  -- Show the integrals are equal (up to commutativity in the exponent)
  have h_integral_eq : ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) =
                       ∫ k0 : ℝ, Complex.exp (-Complex.I * t * k0) / (k0^2 + ω^2) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with k0
    congr 2
    ring

  calc ↑π * ((starRingEnd ℂ) (f x) * f y * ↑(1 / ω) *
        Complex.exp (-(|t| : ℝ) * ω) * Complex.exp (-Complex.I * spatialDot k_spatial r_spatial))
    = (starRingEnd ℂ) (f x) * f y * (↑π * (↑(1 / ω) * Complex.exp (-(|t| : ℝ) * ω))) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by ring
    _ = (starRingEnd ℂ) (f x) * f y * (↑π * (↑(1 / π) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2))) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by rw [h_key]
    _ = (starRingEnd ℂ) (f x) * f y * (∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)) *
        Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) := by
          -- π * (1/π * ...) = (π * 1/π) * ... = 1 * ... = ...
          have h1 : (↑π * (↑(1 / π) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)))
                  = (↑π * ↑(1 / π)) * ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2) := by ring
          rw [h1, h_pi_cancel, one_mul]
    _ = (starRingEnd ℂ) (f x) * f y *
        (Complex.exp (-Complex.I * spatialDot k_spatial r_spatial) *
          ∫ k0 : ℝ, Complex.exp (-Complex.I * k0 * t) / (k0^2 + ω^2)) := by ring

end

end OS3MixedRep

/-! ### From `OS/OS3_ReflectionPositivity.lean` -/

section OS3ReflectionPositivity

open MeasureTheory Complex Matrix OSforGFF
open scoped Real InnerProductSpace BigOperators ComplexOrder Kronecker

noncomputable section

namespace QFT

/-- A complex matrix has nonneg Hermitian quadratic form:
    `Re(∑ᵢⱼ v̄ᵢ vⱼ Mᵢⱼ) ≥ 0` for all `v`.
    This avoids `Matrix.PosSemidef` which requires `PartialOrder ℂ`.
    (Duplicated from `OS/OS3_ReflectionPositivity.lean`, where it remains `private` in
    service of the live reflection-positivity chain.) -/
def IsRePSD {n : ℕ} (M : Fin n → Fin n → ℂ) : Prop :=
  ∀ v : Fin n → ℂ, 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j).re

/-- The quadratic form `star v ⬝ᵥ (of M *ᵥ v)` equals the double sum
    `∑ i, ∑ j, conj(v i) * v j * M i j`.
    (Duplicated from `OS/OS3_ReflectionPositivity.lean`, where it remains `private` in
    service of the live reflection-positivity chain.) -/
lemma quadForm_eq_double_sum
    {n : ℕ} (M : Fin n → Fin n → ℂ) (v : Fin n → ℂ) :
    star v ⬝ᵥ (Matrix.of M *ᵥ v) =
    ∑ i, ∑ j, starRingEnd ℂ (v i) * v j * M i j := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, starRingEnd_apply]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j; ring

/-- Bridge: `Matrix.PosSemidef` over `ℂ` implies `IsRePSD`. -/
lemma isRePSD_of_posSemidef
    {n : ℕ} {M : Fin n → Fin n → ℂ} (hM : (Matrix.of M).PosSemidef) :
    IsRePSD M := by
  intro v
  have h := hM.dotProduct_mulVec_nonneg v
  rw [quadForm_eq_double_sum] at h
  exact (Complex.nonneg_iff.mp h).1

end QFT

end

end OS3ReflectionPositivity

/-! ### From `OS/OS4_Clustering.lean` -/

section OS4Clustering

open MeasureTheory Complex OSforGFF
open scoped Real BigOperators SchwartzMap

noncomputable section

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]

/-- Covariance clustering property: the 2-point function decays at large separations. -/
def CovarianceClustering_real (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (f g : (SchwartzTestFunction d)) (ε : ℝ), ε > 0 →
    ∃ R > 0, ∀ a : (SpaceTime d), ‖a‖ > R →
      ‖SchwingerFunction₂ dμ_config f (g.translate a)‖ < ε

/-- The free covariance has the clustering property. -/
theorem freeCovarianceClustering_real (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    CovarianceClustering_real (gaussianFreeField_free (d := d) m) := by
  intro f g ε hε
  exact schwartz_cross_covariance_decay_real m f g ε hε

end QFT

end

end OS4Clustering

/-! ### From `Covariance/Propagator.lean` -/

section CovariancePropagator

open MeasureTheory Real Complex
open scoped RealInnerProductSpace
open OSforGFF

noncomputable section

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- The covariance kernel is invariant under simultaneous isometric moves of both points:
    for a linear isometry `R` and translation `t`, `C(Rx + t, Ry + t) = C(x, y)`. -/
lemma freeCovariance_isometry_invariant
    (R : LinearIsometry (RingHom.id ℝ) (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (t : EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) :
    freeCovariance d m (R x + t) (R y + t) = freeCovariance d m x y := by
  unfold freeCovariance
  rw [show R x + t - (R y + t) = R (x - y) by rw [map_sub]; abel, R.norm_map]

end

end CovariancePropagator

