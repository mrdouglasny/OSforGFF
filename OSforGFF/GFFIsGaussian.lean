/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.OS0_GFF
import OSforGFF.GaussianMoments

/-!
## Complex GFF Results via OS0 Analyticity

This file proves the essential theorems for Gaussian Free Fields using OS0's
derivative interchange machinery. The key insight is that OS0 already proves
`hasFDerivAt_integral_of_dominated_of_fderiv_le`, which gives us:
  fderiv(∫ f z ω dμ) = ∫ fderiv(f z ω) dμ

### Main Results:
1. `gff_two_point_equals_covarianceℂ_free`: S₂(f,g) = freeCovarianceℂ(f,g)
2. `gff_complex_generating`: Z[J] = exp(-½ S₂(J,J))
3. `isGaussianGJ_gaussianFreeField_free`: The free GFF is Gaussian

### Proof Strategy:
From `gff_real_characteristic`: Z[tf+sg] = exp(-½ Q(tf+sg, tf+sg))
Expanding: = exp(-½(t²Q(f,f) + 2ts Q(f,g) + s²Q(g,g)))
Computing ∂²/∂t∂s|₀ from Gaussian formula: = -Q(f,g)
Computing ∂²/∂t∂s|₀ from integral (OS0 interchange): = -∫⟨ω,f⟩⟨ω,g⟩dμ = -S₂(f,g)
Hence S₂(f,g) = Q(f,g) = freeCovarianceℂ_bilinear(f,g)
-/

open MeasureTheory Complex QFT

noncomputable section

/-! ## Main Results -/

namespace GFFIsGaussian

variable (m : ℝ) [Fact (0 < m)]

/-- For the Gaussian Free Field measure, the product of two complex pairings with test functions
    is integrable. Uses the direct 2-point theorem from GaussianMoments. -/
lemma gaussian_pairing_product_integrable_free_core
    (φ ψ : TestFunctionℂ) :
    Integrable (fun ω => distributionPairingℂ_real ω φ * distributionPairingℂ_real ω ψ)
      (gaussianFreeField_free m).toMeasure :=
  gaussian_pairing_product_integrable_free_2point m φ ψ

/-! ## Core Theorems

The proofs use OS0's derivative interchange machinery:
1. `gff_real_characteristic` gives Z[f] = exp(-½ Q(f,f)) for real f
2. `gaussianFreeField_satisfies_OS0` gives analyticity of Z
3. `hasFDerivAt_integral_of_dominated_of_fderiv_le` (used in OS0) gives derivative interchange
4. Computing ∂²Z/∂t∂s|₀ two ways (Gaussian formula vs integral) gives S₂ = Q
-/

/-- Bilinearity expansion of Q(tf+sg, tf+sg).
    Q(tf+sg, tf+sg) = t²Q(f,f) + 2ts Q(f,g) + s²Q(g,g) -/
lemma freeCovarianceFormR_bilinear_expand (f g : TestFunction) (t s : ℝ) :
    freeCovarianceFormR m (t • f + s • g) (t • f + s • g) =
      t^2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
      s^2 * freeCovarianceFormR m g g := by
  -- Expand using add_left/right and smul_left/right
  calc freeCovarianceFormR m (t • f + s • g) (t • f + s • g)
    _ = freeCovarianceFormR m (t • f) (t • f + s • g) +
        freeCovarianceFormR m (s • g) (t • f + s • g) := by
          rw [freeCovarianceFormR_add_left]
    _ = freeCovarianceFormR m (t • f) (t • f) + freeCovarianceFormR m (t • f) (s • g) +
        (freeCovarianceFormR m (s • g) (t • f) + freeCovarianceFormR m (s • g) (s • g)) := by
          rw [freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    _ = t * freeCovarianceFormR m f (t • f) + t * freeCovarianceFormR m f (s • g) +
        (s * freeCovarianceFormR m g (t • f) + s * freeCovarianceFormR m g (s • g)) := by
          simp only [freeCovarianceFormR_smul_left]
    _ = t * (t * freeCovarianceFormR m f f) + t * (s * freeCovarianceFormR m f g) +
        (s * (t * freeCovarianceFormR m g f) + s * (s * freeCovarianceFormR m g g)) := by
          simp only [freeCovarianceFormR_smul_right]
    _ = t^2 * freeCovarianceFormR m f f + 2 * t * s * freeCovarianceFormR m f g +
        s^2 * freeCovarianceFormR m g g := by
          -- Use symmetry: Q(g,f) = Q(f,g)
          have hsym : freeCovarianceFormR m g f = freeCovarianceFormR m f g :=
            freeCovarianceFormR_symm m g f
          rw [hsym]; ring

/-- The Gaussian CF formula for two test functions. -/
lemma gff_cf_two_testfunctions (f g : TestFunction) (t s : ℝ) :
    GJGeneratingFunctional (gaussianFreeField_free m) (t • f + s • g) =
      Complex.exp (-(1/2 : ℂ) * (t^2 * freeCovarianceFormR m f f +
        2 * t * s * freeCovarianceFormR m f g + s^2 * freeCovarianceFormR m g g)) := by
  have h := gff_real_characteristic m (t • f + s • g)
  rw [freeCovarianceFormR_bilinear_expand] at h
  convert h using 2
  push_cast; ring

/-! ## OS0-Based Derivative Machinery

The following lemmas use OS0's analyticity to compute mixed derivatives. -/

/-- OS0 specialized to two test functions gives analyticity of Z[tf + sg] in (t,s) ∈ ℂ² -/
lemma gff_two_param_analytic (f g : TestFunction) :
    AnalyticOn ℂ (fun z : Fin 2 → ℂ =>
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) (z 0 • toComplex f + z 1 • toComplex g))
      Set.univ := by
  -- Direct application of gaussianFreeField_satisfies_OS0 with n=2, J = ![toComplex f, toComplex g]
  have h := gaussianFreeField_satisfies_OS0 m 2 ![toComplex f, toComplex g]
  convert h using 2
  -- Goal: GJGeneratingFunctionalℂ _ (z 0 • toComplex f + z 1 • toComplex g) =
  --       GJGeneratingFunctionalℂ _ (∑ i, z i • ![toComplex f, toComplex g] i)
  -- μ_GFF m = gaussianFreeField_free m by definition (abbrev)
  -- For the test function argument, use Fin.sum_univ_two
  congr 1
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## OS0-Based Complex Extension via Identity Theorem

The key insight is that we can extend from real to complex test functions using:
1. OS0 gives analyticity of Z[z₀f + z₁g] in (z₀, z₁) ∈ ℂ²
2. For real parameters, we have the Gaussian formula
3. The Gaussian formula defines an entire function of (z₀, z₁)
4. By the identity theorem (applied twice in 1D), the two analytic functions agree everywhere

This eliminates the need for the `twoD_line_from_realCF` axiom from MinlosAnalytic. -/

/-- Key technical lemma: fixing one coordinate, the slice is analytic in the other.
    For z₀ ↦ Z[z₀•f + t•g] where t is a fixed complex number.
    Derived from OS0 by composition with linear embedding z₀ ↦ ![z₀, t]. -/
lemma gff_slice_analytic_z0 (f g : TestFunction) (t : ℂ) :
    AnalyticOnNhd ℂ (fun z₀ : ℂ =>
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) (z₀ • toComplex f + t • toComplex g))
      Set.univ := by
  -- From gff_two_param_analytic, the function F(z) = Z[z₀•f + z₁•g] is analytic on (Fin 2 → ℂ)
  have h2param := gff_two_param_analytic m f g
  -- The embedding e(z₀) = ![z₀, t] is analytic
  let e : ℂ → (Fin 2 → ℂ) := fun z₀ => ![z₀, t]
  have he_an : AnalyticOn ℂ e Set.univ := by
    intro x _
    rw [analyticWithinAt_univ]
    apply AnalyticAt.pi
    intro i
    fin_cases i
    · exact analyticAt_id
    · exact analyticAt_const
  -- Composition is analytic
  have hcomp : AnalyticOn ℂ (fun z₀ : ℂ =>
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) (z₀ • toComplex f + t • toComplex g))
      Set.univ := by
    have hc := AnalyticOn.comp h2param he_an (fun _ _ => trivial)
    convert hc using 2
  -- AnalyticOn on univ → AnalyticOnNhd on univ
  exact analyticOn_univ.mp hcomp

/-- Derived from gff_slice_analytic_z0 by swapping f ↔ g and using add_comm. -/
lemma gff_slice_analytic_z1 (f g : TestFunction) (z₀ : ℂ) :
    AnalyticOnNhd ℂ (fun z₁ : ℂ =>
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) (z₀ • toComplex f + z₁ • toComplex g))
      Set.univ := by
  have h := gff_slice_analytic_z0 m g f z₀
  simp only [add_comm (z₀ • toComplex f)] at h ⊢
  convert h using 2

omit [Fact (0 < m)] in
/-- Slice of Gaussian RHS is analytic (exp of polynomial). -/
lemma gaussian_rhs_slice_analytic_z0 (f g : TestFunction) (t : ℂ) :
    AnalyticOnNhd ℂ (fun z₀ : ℂ =>
      Complex.exp (-(1/2 : ℂ) * (z₀^2 * freeCovarianceFormR m f f +
        2 * z₀ * t * freeCovarianceFormR m f g + t^2 * freeCovarianceFormR m g g)))
      Set.univ := by
  apply AnalyticOnNhd.cexp
  apply AnalyticOnNhd.mul analyticOnNhd_const
  apply AnalyticOnNhd.add
  apply AnalyticOnNhd.add
  · apply AnalyticOnNhd.mul _ (analyticOnNhd_const (v := (freeCovarianceFormR m f f : ℂ)))
    exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2
  · -- 2 * z₀ * t * Q(f,g)
    have h1 : AnalyticOnNhd ℂ (fun z₀ : ℂ => 2 * z₀ * t * freeCovarianceFormR m f g) Set.univ := by
      have : AnalyticOnNhd ℂ (fun z₀ : ℂ => (2 * t * freeCovarianceFormR m f g) * z₀) Set.univ :=
        AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
      convert this using 2
      ring
    exact h1
  · exact analyticOnNhd_const

omit [Fact (0 < m)] in
/-- Slice of Gaussian RHS is analytic in the second variable. -/
lemma gaussian_rhs_slice_analytic_z1 (f g : TestFunction) (z₀ : ℂ) :
    AnalyticOnNhd ℂ (fun z₁ : ℂ =>
      Complex.exp (-(1/2 : ℂ) * (z₀^2 * freeCovarianceFormR m f f +
        2 * z₀ * z₁ * freeCovarianceFormR m f g + z₁^2 * freeCovarianceFormR m g g)))
      Set.univ := by
  apply AnalyticOnNhd.cexp
  apply AnalyticOnNhd.mul analyticOnNhd_const
  apply AnalyticOnNhd.add
  apply AnalyticOnNhd.add
  · exact analyticOnNhd_const
  · -- 2 * z₀ * z₁ * Q(f,g)
    have h1 : AnalyticOnNhd ℂ (fun z₁ : ℂ => 2 * z₀ * z₁ * freeCovarianceFormR m f g) Set.univ := by
      have : AnalyticOnNhd ℂ (fun z₁ : ℂ => (2 * z₀ * freeCovarianceFormR m f g) * z₁) Set.univ :=
        AnalyticOnNhd.mul analyticOnNhd_const analyticOnNhd_id
      convert this using 2
      ring
    exact h1
  · apply AnalyticOnNhd.mul _ (analyticOnNhd_const (v := (freeCovarianceFormR m g g : ℂ)))
    exact (analyticOnNhd_id (𝕜 := ℂ)).pow 2

/-- The GFF CF and Gaussian formula agree on ℝ².
    This follows from gff_cf_two_testfunctions by converting between types. -/
lemma gff_cf_agrees_on_reals_OS0 (f g : TestFunction) (t s : ℝ) :
    GJGeneratingFunctionalℂ (gaussianFreeField_free m) ((t : ℂ) • toComplex f + (s : ℂ) • toComplex g) =
      Complex.exp (-(1/2 : ℂ) * ((t : ℂ)^2 * freeCovarianceFormR m f f +
        2 * (t : ℂ) * (s : ℂ) * freeCovarianceFormR m f g + (s : ℂ)^2 * freeCovarianceFormR m g g)) := by
  -- Use the real version gff_cf_two_testfunctions and convert
  have h := gff_cf_two_testfunctions m f g t s
  -- First note: t • f + s • g is real, so toComplex (t • f + s • g) = t • toComplex f + s • toComplex g
  have h_eq_test : (t : ℂ) • toComplex f + (s : ℂ) • toComplex g = toComplex (t • f + s • g) := by
    ext x
    simp [toComplex_apply]
  rw [h_eq_test]
  -- GJGeneratingFunctionalℂ on a real test function equals GJGeneratingFunctional
  rw [GJGeneratingFunctionalℂ_toComplex, h]

/-- Complex generating functional for the free GFF via OS0 + identity theorem.
    This proves the result WITHOUT using twoD_line_from_realCF. -/
theorem gff_complex_characteristic_OS0 :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
        Complex.exp (-(1/2 : ℂ) * freeCovarianceℂ_bilinear m J J) := by
  intro J
  -- Decompose J = f + I*g where f, g are real test functions
  let f := (complex_testfunction_decompose J).1
  let g := (complex_testfunction_decompose J).2
  have hJ : J = toComplex f + Complex.I • toComplex g := by
    ext x
    simpa [f, g, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose J x

  -- Define the LHS and RHS as functions of two complex variables
  let F : ℂ → ℂ → ℂ := fun z₀ z₁ =>
    GJGeneratingFunctionalℂ (gaussianFreeField_free m) (z₀ • toComplex f + z₁ • toComplex g)
  let G : ℂ → ℂ → ℂ := fun z₀ z₁ =>
    Complex.exp (-(1/2 : ℂ) * (z₀^2 * freeCovarianceFormR m f f +
      2 * z₀ * z₁ * freeCovarianceFormR m f g + z₁^2 * freeCovarianceFormR m g g))

  -- Step 1: F and G agree on ℝ²
  have h_agree_real : ∀ t s : ℝ, F t s = G t s := by
    intro t s
    simp only [F, G]
    exact gff_cf_agrees_on_reals_OS0 m f g t s

  -- Step 2: For fixed real s, F(·, s) and G(·, s) are entire and agree on ℝ
  -- By 1D identity theorem: F(z₀, s) = G(z₀, s) for all z₀ ∈ ℂ
  have h_step1 : ∀ (s : ℝ) (z₀ : ℂ), F z₀ s = G z₀ s := by
    intro s z₀
    -- Both slices are entire
    have hF_an : AnalyticOnNhd ℂ (fun z₀ => F z₀ s) Set.univ := gff_slice_analytic_z0 m f g s
    have hG_an : AnalyticOnNhd ℂ (fun z₀ => G z₀ s) Set.univ := gaussian_rhs_slice_analytic_z0 m f g s
    -- They agree on ℝ which has accumulation points in ℂ
    have h_agree_slice : ∀ t : ℝ, F t s = G t s := fun t => h_agree_real t s
    -- Apply 1D identity theorem
    have h_eq : (fun z₀ => F z₀ s) = (fun z₀ => G z₀ s) := by
      apply AnalyticOnNhd.eq_of_frequently_eq hF_an hG_an (z₀ := 0)
      -- ℝ has accumulation points at 0 in ℂ: for any neighborhood of 0, there exist nonzero reals
      simp only [Filter.Frequently]
      intro hU
      -- hU : ∀ᶠ (x : ℂ) in nhdsWithin 0 {0}ᶜ, F x s ≠ G x s
      -- This means {x | F x s ≠ G x s} ∈ nhdsWithin 0 {0}ᶜ
      rw [Filter.Eventually, mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
      -- ε/2 is a nonzero real in V ∩ {0}ᶜ where F = G, contradicting hU
      have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
      have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
        simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
        linarith)
      have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have h_in : ((ε / 2 : ℝ) : ℂ) ∈ V ∩ {(0 : ℂ)}ᶜ := ⟨h_mem_V, h_ne⟩
      exact hV_sub h_in (h_agree_slice (ε / 2))
    exact congrFun h_eq z₀

  -- Step 3: For fixed z₀ ∈ ℂ, F(z₀, ·) and G(z₀, ·) agree on ℝ (by step 2)
  -- By 1D identity theorem: F(z₀, z₁) = G(z₀, z₁) for all z₁ ∈ ℂ
  have h_step2 : ∀ z₀ z₁ : ℂ, F z₀ z₁ = G z₀ z₁ := by
    intro z₀ z₁
    have hF_an : AnalyticOnNhd ℂ (fun z₁ => F z₀ z₁) Set.univ := gff_slice_analytic_z1 m f g z₀
    have hG_an : AnalyticOnNhd ℂ (fun z₁ => G z₀ z₁) Set.univ := gaussian_rhs_slice_analytic_z1 m f g z₀
    have h_agree_slice : ∀ s : ℝ, F z₀ s = G z₀ s := fun s => h_step1 s z₀
    have h_eq : (fun z₁ => F z₀ z₁) = (fun z₁ => G z₀ z₁) := by
      apply AnalyticOnNhd.eq_of_frequently_eq hF_an hG_an (z₀ := 0)
      simp only [Filter.Frequently]
      intro hU
      rw [Filter.Eventually, mem_nhdsWithin] at hU
      obtain ⟨V, hV_open, h0_in_V, hV_sub⟩ := hU
      obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hV_open 0 h0_in_V
      have h_half_pos : (0 : ℝ) < ε / 2 := half_pos hε_pos
      have h_mem_V : ((ε / 2 : ℝ) : ℂ) ∈ V := hε_ball (by
        simp only [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real]
        rw [Real.norm_eq_abs, abs_of_pos h_half_pos]
        linarith)
      have h_ne : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        linarith
      have h_in : ((ε / 2 : ℝ) : ℂ) ∈ V ∩ {(0 : ℂ)}ᶜ := ⟨h_mem_V, h_ne⟩
      exact hV_sub h_in (h_agree_slice (ε / 2))
    exact congrFun h_eq z₁

  -- Step 4: Evaluate at (1, I) to get J = f + I*g
  have h_eval : F 1 Complex.I = G 1 Complex.I := h_step2 1 Complex.I

  -- Step 5: Simplify LHS
  have h_LHS : GJGeneratingFunctionalℂ (gaussianFreeField_free m) J = F 1 Complex.I := by
    simp only [F, hJ]
    congr 1
    simp [one_smul]

  -- Step 6: Simplify RHS using Qc formula
  have h_RHS : Complex.exp (-(1/2 : ℂ) * freeCovarianceℂ_bilinear m J J) = G 1 Complex.I := by
    simp only [G]
    congr 1
    -- freeCovarianceℂ_bilinear of J = f + I*g
    -- Qc(f+Ig, f+Ig) = Q(f,f) - Q(g,g) + 2I*Q(f,g)
    -- Compare with: 1²Q(f,f) + 2*1*I*Q(f,g) + I²*Q(g,g)
    --             = Q(f,f) + 2I*Q(f,g) - Q(g,g)
    have h_Qc : freeCovarianceℂ_bilinear m J J =
        freeCovarianceFormR m f f - freeCovarianceFormR m g g +
          2 * Complex.I * freeCovarianceFormR m f g := by
      rw [hJ]
      rw [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
          freeCovarianceℂ_bilinear_add_right]
      simp only [freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
      have h_ff := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f f
      have h_fg := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f g
      have h_gf := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) g f
      have h_gg := freeCovarianceℂ_bilinear_agrees_on_reals (m := m) g g
      rw [h_ff, h_fg, h_gf, h_gg]
      have h_sym : freeCovarianceFormR m g f = freeCovarianceFormR m f g :=
        freeCovarianceFormR_symm m g f
      rw [h_sym]
      -- Need: Q(f,f) + I*Q(f,g) + I*Q(f,g) + I*(I*Q(g,g)) = Q(f,f) - Q(g,g) + 2*I*Q(f,g)
      have hII : Complex.I * (Complex.I * (freeCovarianceFormR m g g : ℂ)) =
          -(freeCovarianceFormR m g g : ℂ) := by
        rw [← mul_assoc, Complex.I_mul_I]
        ring
      rw [hII]
      ring
    rw [h_Qc]
    simp only [one_pow, Complex.I_sq, one_mul]
    ring

  rw [h_LHS, h_eval, ← h_RHS]

/-! ## Polarization-Based Proof

The key insight is to use the **polarization identity** instead of derivative calculus.

For a centered Gaussian:
- E[⟨ω,f⟩²] = Q(f,f) (this is `gff_second_moment_eq_covariance` from GFFbridge)

By polarization:
- E[XY] = ¼(E[(X+Y)²] - E[(X-Y)²])
- With X = ⟨ω,f⟩, Y = ⟨ω,g⟩:
  E[⟨ω,f⟩⟨ω,g⟩] = ¼(Q(f+g,f+g) - Q(f-g,f-g)) = Q(f,g)

This avoids all derivative calculus! -/

/-- For real test functions, the second moment equals the covariance.
    S₂(f,g) = Q(f,g) = freeCovarianceFormR(f,g)

    Proof via polarization identity:
    E[XY] = ¼(E[(X+Y)²] - E[(X-Y)²])
         = ¼(Q(f+g,f+g) - Q(f-g,f-g))
         = Q(f,g) by bilinearity -/
theorem schwinger_eq_covariance_real (f g : TestFunction) :
    ∫ ω, (ω f) * (ω g) ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m f g := by
  -- Use polarization identity: XY = ¼((X+Y)² - (X-Y)²)
  have h_polar : ∀ ω : FieldConfiguration,
      (ω f) * (ω g) = (1/4 : ℝ) * ((ω (f + g))^2 - (ω (f - g))^2) := by
    intro ω
    -- Linearity of pairing
    simp only [map_add, map_sub]
    ring
  simp_rw [h_polar]
  rw [MeasureTheory.integral_const_mul]
  -- Use gff_second_moment_eq_covariance for each term
  have h_sq_fg : ∫ ω, (ω (f + g))^2 ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m (f + g) (f + g) := by
    have := gff_second_moment_eq_covariance m (f + g)
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  have h_sq_f_g : ∫ ω, (ω (f - g))^2 ∂(gaussianFreeField_free m).toMeasure =
      freeCovarianceFormR m (f - g) (f - g) := by
    have := gff_second_moment_eq_covariance m (f - g)
    simp only [distributionPairingCLM_apply, distributionPairing] at this
    exact this
  rw [integral_sub, h_sq_fg, h_sq_f_g]
  -- Expand using bilinearity of Q
  -- Q(f+g,f+g) = Q(f,f) + 2Q(f,g) + Q(g,g)
  -- Q(f-g,f-g) = Q(f,f) - 2Q(f,g) + Q(g,g)
  -- Difference = 4Q(f,g)
  -- Use f - g = f + (-1) • g for subtraction
  have h_sub : f - g = f + (-1 : ℝ) • g := by simp [sub_eq_add_neg, neg_smul, one_smul]
  -- Expand Q(f+g, f+g)
  have h_expand_plus : freeCovarianceFormR m (f + g) (f + g) =
      freeCovarianceFormR m f f + 2 * freeCovarianceFormR m f g + freeCovarianceFormR m g g := by
    rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    rw [freeCovarianceFormR_symm m g f]
    ring
  -- Expand Q(f-g, f-g)
  have h_expand_minus : freeCovarianceFormR m (f - g) (f - g) =
      freeCovarianceFormR m f f - 2 * freeCovarianceFormR m f g + freeCovarianceFormR m g g := by
    rw [h_sub]
    rw [freeCovarianceFormR_add_left, freeCovarianceFormR_add_right, freeCovarianceFormR_add_right]
    rw [freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right, freeCovarianceFormR_smul_left,
        freeCovarianceFormR_smul_right]
    rw [freeCovarianceFormR_symm m g f]
    ring
  rw [h_expand_plus, h_expand_minus]
  ring
  -- Integrability for subtraction
  · exact gff_pairing_square_integrable m (f + g)
  · exact gff_pairing_square_integrable m (f - g)

/-- For real test functions embedded into complex, the Schwinger 2-point function
    equals the complex covariance. -/
lemma schwinger_eq_covarianceℂ_on_reals (f g : TestFunction) :
    SchwingerFunctionℂ₂ (gaussianFreeField_free m) (toComplex f) (toComplex g) =
      freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := by
  -- Use distributionPairingℂ_real_toComplex to reduce to real pairings
  simp only [SchwingerFunctionℂ₂, SchwingerFunctionℂ, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    distributionPairingℂ_real_toComplex]
  -- Now we have: ∫ ω, ↑(ω f) * ↑(ω g) dμ = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g)
  -- Step 1: Rewrite ↑a * ↑b = ↑(a * b) pointwise using ofReal_mul
  simp_rw [← Complex.ofReal_mul]
  -- Step 2: Integrability of the product
  have h_int : Integrable (fun ω => distributionPairing ω f * distributionPairing ω g)
      (gaussianFreeField_free m).toMeasure := by
    -- Use Hölder: L² × L² → L¹
    have hf : MemLp (fun ω => distributionPairing ω f) 2 (gaussianFreeField_free m).toMeasure :=
      gaussianFreeField_pairing_memLp m f 2 (by simp)
    have hg : MemLp (fun ω => distributionPairing ω g) 2 (gaussianFreeField_free m).toMeasure :=
      gaussianFreeField_pairing_memLp m g 2 (by simp)
    exact hf.integrable_mul hg
  -- Step 3: Pull cast outside integral: ∫ ↑(f ω) dμ = ↑(∫ f ω dμ)
  rw [integral_ofReal_eq _ _ h_int]
  -- Step 4: Apply the real Schwinger = covariance equality and agreement on reals
  -- Note: ω f is notation for distributionPairing ω f, and convert handles this
  convert congrArg (↑· : ℝ → ℂ) (schwinger_eq_covariance_real m f g) using 2
  · exact freeCovarianceℂ_bilinear_agrees_on_reals m f g

end GFFIsGaussian

/-! ## Main Theorems (at root level for compatibility) -/

/-- For complex test functions, the Schwinger 2-point function equals the complex covariance.

    S₂(μ, f, g) = freeCovarianceℂ_bilinear m f g

    This extends schwinger_eq_covariance_real to complex test functions by bilinearity:
    both S₂ and freeCovarianceℂ_bilinear are bilinear, and they agree on real inputs.

    For any complex f = fRe + I•fIm, g = gRe + I•gIm, we expand by bilinearity. -/
theorem gff_two_point_equals_covarianceℂ_free (m : ℝ) [Fact (0 < m)] (f g : TestFunctionℂ) :
    SchwingerFunctionℂ₂ (gaussianFreeField_free m) f g = freeCovarianceℂ_bilinear m f g := by
  -- Decompose complex test functions into real and imaginary parts
  let fRe := (complex_testfunction_decompose f).1
  let fIm := (complex_testfunction_decompose f).2
  let gRe := (complex_testfunction_decompose g).1
  let gIm := (complex_testfunction_decompose g).2
  let frC := toComplex fRe
  let fiC := toComplex fIm
  let grC := toComplex gRe
  let giC := toComplex gIm
  -- Prove the decompositions: f = frC + I • fiC, g = grC + I • giC
  have hf : f = frC + Complex.I • fiC := by
    ext x
    simpa [frC, fiC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose f x
  have hg : g = grC + Complex.I • giC := by
    ext x
    simpa [grC, giC, toComplex_apply, smul_eq_mul, complex_testfunction_decompose]
      using complex_testfunction_decompose_recompose g x
  rw [hf, hg]
  -- Extract bilinearity properties from CovarianceBilinear
  -- CovarianceBilinear gives: ∀ c φ₁ φ₂ ψ,
  --   .1: S₂(c • φ₁, ψ) = c * S₂(φ₁, ψ)
  --   .2.1: S₂(φ₁ + φ₂, ψ) = S₂(φ₁, ψ) + S₂(φ₂, ψ)
  --   .2.2.1: S₂(φ₁, c • ψ) = c * S₂(φ₁, ψ)
  --   .2.2.2: S₂(φ₁, ψ + φ₂) = S₂(φ₁, ψ) + S₂(φ₁, φ₂)
  have h_bilin := covariance_bilinear_from_general m
  have S2_smul_left : ∀ (c : ℂ) a b, SchwingerFunctionℂ₂ (gaussianFreeField_free m) (c • a) b =
      c * SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b :=
    fun c a b => (h_bilin c a 0 b).1
  have S2_add_left : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeField_free m) (a + b) c =
      SchwingerFunctionℂ₂ (gaussianFreeField_free m) a c + SchwingerFunctionℂ₂ (gaussianFreeField_free m) b c :=
    fun a b c => (h_bilin 1 a b c).2.1
  have S2_smul_right : ∀ (c : ℂ) a b, SchwingerFunctionℂ₂ (gaussianFreeField_free m) a (c • b) =
      c * SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b :=
    fun c a b => (h_bilin c a 0 b).2.2.1
  have S2_add_right : ∀ a b c, SchwingerFunctionℂ₂ (gaussianFreeField_free m) a (b + c) =
      SchwingerFunctionℂ₂ (gaussianFreeField_free m) a b + SchwingerFunctionℂ₂ (gaussianFreeField_free m) a c :=
    fun a b c => (h_bilin 1 a c b).2.2.2
  -- Expand LHS: S₂(frC + I•fiC, grC + I•giC)
  rw [S2_add_left, S2_add_right, S2_add_right, S2_smul_left, S2_smul_left, S2_smul_right,
      S2_smul_right]
  -- Expand RHS: freeCovarianceℂ_bilinear(frC + I•fiC, grC + I•giC)
  simp only [freeCovarianceℂ_bilinear_add_left, freeCovarianceℂ_bilinear_add_right,
    freeCovarianceℂ_bilinear_smul_left, freeCovarianceℂ_bilinear_smul_right]
  -- Both sides have 4 terms. Rewrite S₂(toComplex ?, toComplex ?) = C(toComplex ?, toComplex ?)
  -- frC = toComplex fRe, fiC = toComplex fIm, grC = toComplex gRe, giC = toComplex gIm
  rw [GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fRe gRe,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fRe gIm,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fIm gRe,
      GFFIsGaussian.schwinger_eq_covarianceℂ_on_reals m fIm gIm]
  -- Now both sides are equal up to commutativity of addition
  ring

/-- Complex generating functional for the free GFF: Z[J] = exp(-½ S₂(J,J))

    This follows from gff_real_characteristic (for real J) extended to complex J
    via analyticity (gaussianFreeField_satisfies_OS0). Both sides are analytic in J
    and agree on real J, hence they are equal everywhere. -/
theorem gff_complex_generating (m : ℝ) [Fact (0 < m)] :
    ∀ J : TestFunctionℂ,
      GJGeneratingFunctionalℂ (gaussianFreeField_free m) J =
        Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ (gaussianFreeField_free m) J J) := by
  intro J
  -- Use gff_two_point_equals_covarianceℂ_free: S₂ = freeCovarianceℂ_bilinear
  rw [gff_two_point_equals_covarianceℂ_free]
  -- Now goal is: Z[J] = exp(-½ freeCovarianceℂ_bilinear m J J)
  -- Use gff_complex_characteristic_OS0 (via OS0 + identity theorem, no MinlosAnalytic dependency)
  exact GFFIsGaussian.gff_complex_characteristic_OS0 m J

/-- The Gaussian Free Field constructed via Minlos is Gaussian.

    This combines:
    1. Centering: E[⟨ω,φ⟩] = 0 (from gaussianFreeField_free_centered)
    2. Gaussian CF: Z[J] = exp(-½ S₂(J,J)) (from gff_complex_generating) -/
theorem isGaussianGJ_gaussianFreeField_free (m : ℝ) [Fact (0 < m)] :
    isGaussianGJ (gaussianFreeField_free m) := by
  constructor
  · exact gaussianFreeField_free_centered m
  · exact fun J => gff_complex_generating m J
