/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Spacetime.Basic


open MeasureTheory SchwartzMap Real Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Time-slice machinery for `SpaceTime d`

The time coordinate of `x : SpaceTime d` is accessed via `x 0`.
These lemmas match the signatures needed in OS3_MixedRepInfra.lean.
-/

section TimeSlice

variable {d : ℕ} [Fact (2 ≤ d)]

/-- Decomposition of spacetime as time × space: `(t, x) ↦ (t, x₁, …, x_{d-1})`. -/
noncomputable def spacetimeOfTimeSpace (t : ℝ) (x : SpatialCoords d) : SpaceTime d :=
  EuclideanSpace.equiv (Fin d) ℝ |>.symm fun i =>
    Fin.cons (α := fun _ => ℝ) t (fun j => x j)
      (Fin.cast (by have h : 2 ≤ d := Fact.out; omega) i)

/-- The time coordinate of spacetimeOfTimeSpace is t. -/
lemma spacetimeOfTimeSpace_time (t : ℝ) (x : SpatialCoords d) :
    (spacetimeOfTimeSpace t x) 0 = t := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- Access the i-th spatial component of spacetimeOfTimeSpace.
    Mathematical fact: (spacetimeOfTimeSpace t x) (i+1) = x i -/
lemma spacetimeOfTimeSpace_spatial (t : ℝ) (x : SpatialCoords d) (i : Fin (d - 1)) :
    (spacetimeOfTimeSpace t x) ⟨i.val + 1, by have := i.isLt; omega⟩ = x i := rfl

/-- The decomposition: spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbed x.
    This is the key structural fact: (t, x) = (t, 0) + (0, x). -/
lemma spacetimeOfTimeSpace_decompose (t : ℝ) (x : SpatialCoords d) :
    spacetimeOfTimeSpace t x = spacetimeOfTimeSpace t 0 + spacetimeOfTimeSpace 0 x := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext j
  cases' j using Fin.cases with j
  · -- time coordinate
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
  · -- spatial coordinates
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- Norm comparison: the spacetime norm dominates the spatial norm. -/
lemma spacetimeOfTimeSpace_norm_ge (t : ℝ) (x : SpatialCoords d) :
    ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖ := by
  have hsq : ‖spacetimeOfTimeSpace t x‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    congr 1
    · rw [show (spacetimeOfTimeSpace t x).ofLp 0 = t from spacetimeOfTimeSpace_time t x]
      simp [Real.norm_eq_abs, sq_abs]
    · rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show (spacetimeOfTimeSpace t x).ofLp j.succ = x j from rfl]
  have hsq_le : ‖x‖ ^ 2 ≤ ‖spacetimeOfTimeSpace t x‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg t]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hy : 0 ≤ ‖spacetimeOfTimeSpace t x‖ := norm_nonneg _
  exact (sq_le_sq₀ hx hy).mp hsq_le

/-- Linear embedding of space into spacetime as the spatial subspace at time 0.
    This maps x ↦ (0, x₁, …, x_{d-1}), i.e., spacetimeOfTimeSpace 0 x. -/
noncomputable def spatialEmbed : SpatialCoords d →ₗ[ℝ] SpaceTime d where
  toFun := fun x => spacetimeOfTimeSpace 0 x
  map_add' := fun x y => by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    ext j
    cases' j using Fin.cases with j
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
  map_smul' := fun r x => by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    ext j
    cases' j using Fin.cases with j
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- The spatial embedding is continuous (being linear on finite-dim spaces). -/
lemma spatialEmbed_continuous : Continuous (spatialEmbed (d := d)) :=
  LinearMap.continuous_of_finiteDimensional spatialEmbed

/-- The spatial embedding as a CLM. -/
noncomputable def spatialEmbedCLM : SpatialCoords d →L[ℝ] SpaceTime d :=
  ⟨spatialEmbed, spatialEmbed_continuous⟩

/-- The time-origin point `(t, 0, …, 0)`. -/
noncomputable def timeOrigin (t : ℝ) : SpaceTime d :=
  spacetimeOfTimeSpace t 0

/-- spacetimeOfTimeSpace is continuous in the spatial argument for fixed time. -/
lemma continuous_spacetimeOfTimeSpace_right (t : ℝ) :
    Continuous (spacetimeOfTimeSpace (d := d) t) := by
  -- spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbedCLM x
  -- The first term is constant, the second is a CLM applied to x
  have h_decompose : ∀ x : SpatialCoords d,
      spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbedCLM x := by
    intro x
    rw [spacetimeOfTimeSpace_decompose]
    rfl
  have h_cont : Continuous (fun x : SpatialCoords d => timeOrigin t + spatialEmbedCLM x) :=
    continuous_const.add spatialEmbedCLM.continuous
  exact (continuous_congr h_decompose).mpr h_cont

/-- The time-axis point `(s, 0, …, 0)` is `s` times the time unit vector. -/
lemma spacetimeOfTimeSpace_eq_smul_single (s : ℝ) :
    spacetimeOfTimeSpace (d := d) s 0 = s • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext j
  cases' j using Fin.cases with j
  · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases,
          EuclideanSpace.single_apply]
  · have hne : Fin.succ j ≠ 0 := Fin.succ_ne_zero j
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases,
          EuclideanSpace.single_apply, hne]

/-- The polynomial decay `1/(1+‖x‖)^d` is integrable on the spatial slice `ℝ^(d-1)`
    (the exponent `d` exceeds the dimension `d - 1`). -/
lemma polynomial_decay_integrable_spatial :
    Integrable (fun x : SpatialCoords d => 1 / (1 + ‖x‖) ^ d) volume := by
  have h1d : 1 ≤ d := by have h : 2 ≤ d := Fact.out; omega
  have hdim_lt : (Module.finrank ℝ (SpatialCoords d) : ℝ) < ((d : ℕ) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [h1d]; ring
    rw [this]; linarith
  have h_int := integrable_one_add_norm (E := SpatialCoords d) (μ := volume)
    (r := ((d : ℕ) : ℝ)) hdim_lt
  convert h_int using 1
  ext x
  have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  simp only [Real.rpow_neg (le_of_lt h_pos), one_div]
  congr 1
  exact (Real.rpow_natCast (1 + ‖x‖) d).symm

/-- The spatial integral G(t) = ∫ ‖f(t, x)‖ dx over the spatial slice. -/
noncomputable def spatialNormIntegral (f : SchwartzTestFunctionℂ d) (t : ℝ) : ℝ :=
  ∫ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖

/-- G(t) = 0 for t ≤ 0 when f vanishes on {t ≤ 0}. -/
lemma spatialNormIntegral_zero_of_neg (f : SchwartzTestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) (t : ℝ) (ht : t ≤ 0) :
    spatialNormIntegral f t = 0 := by
  simp only [spatialNormIntegral]
  have h_zero : ∀ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖ = 0 := by
    intro x
    have h : (spacetimeOfTimeSpace t x) 0 ≤ 0 := by
      rw [spacetimeOfTimeSpace_time]; exact ht
    simp [hf_supp _ h]
  simp [h_zero]

/-- G(t) is nonnegative. -/
lemma spatialNormIntegral_nonneg (f : SchwartzTestFunctionℂ d) (t : ℝ) :
    0 ≤ spatialNormIntegral f t :=
  integral_nonneg (fun _ => norm_nonneg _)

/-! ### Order-N boundary-vanishing bounds

A Schwartz function that vanishes on the closed half-space `{x₀ ≤ 0}` is flat to all orders at
the time boundary: its time derivative is again a Schwartz function vanishing on the half-space,
so integrating repeatedly along the time direction upgrades the linear bound `‖f‖ ≲ t` to
`‖f‖ ≲ tᴺ` for every order `N` — uniformly in the spatial coordinates, with polynomial spatial
decay `(1 + ‖x̄‖)⁻ᵈ`.
-/

omit [Fact (2 ≤ d)] in
/-- Pointwise polynomial decay of a Schwartz function: `‖f y‖ ≤ C / (1 + ‖y‖)^d`. -/
lemma schwartz_pointwise_decay_bound (f : SchwartzTestFunctionℂ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : SpaceTime d, ‖f y‖ ≤ C / (1 + ‖y‖) ^ d := by
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ y : SpaceTime d, (1 + ‖y‖) ^ d * ‖f y‖ ≤ S :=
    ⟨_, fun y => by
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := ((d, 0) : ℕ × ℕ))
        (k := d) (n := 0) le_rfl le_rfl f y
      rwa [norm_iteratedFDeriv_zero] at h⟩
  have hS_nonneg : 0 ≤ S := le_trans (by positivity) (hS 0)
  refine ⟨S + 1, by linarith, fun y => ?_⟩
  have h1y_pow : (0 : ℝ) < (1 + ‖y‖) ^ d := pow_pos (by linarith [norm_nonneg y]) d
  rw [le_div_iff₀ h1y_pow]
  calc ‖f y‖ * (1 + ‖y‖) ^ d = (1 + ‖y‖) ^ d * ‖f y‖ := by ring
    _ ≤ S := hS y
    _ ≤ S + 1 := by linarith

/-- Every spacetime point is recovered from its time and spatial components:
    `x = (x₀, x̄)` with `x₀ = x 0` and `x̄ = spatialPart x`. -/
lemma spacetimeOfTimeSpace_spatialPart (x : SpaceTime d) :
    spacetimeOfTimeSpace (x 0) (spatialPart x) = x := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext j
  cases' j using Fin.cases with j
  · exact spacetimeOfTimeSpace_time _ _
  · rfl

/-- If a Schwartz function vanishes on the closed half-space `{x₀ ≤ 0}`, so does its time
    derivative `x ↦ (fderiv ℝ f x) e₀`: along the time line through such a point the function
    is identically zero for nonpositive times, so the (unique) derivative within that ray
    vanishes. -/
lemma schwartz_vanishing_fderiv_time (f : SchwartzTestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0)
    (x : SpaceTime d) (hx : x 0 ≤ 0) :
    fderiv ℝ f x (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) = 0 := by
  set e₀ : SpaceTime d := EuclideanSpace.single (0 : Fin d) (1 : ℝ) with he₀
  have h_time : ∀ s : ℝ, (x + s • e₀) 0 = x 0 + s := by
    intro s
    simp [he₀]
  have h_vanish : ∀ s ∈ Set.Iic (0 : ℝ), f (x + s • e₀) = 0 := fun s hs =>
    hf_supp _ (by rw [h_time s]; exact add_nonpos hx hs)
  have h_path : HasDerivAt (fun s : ℝ => x + s • e₀) e₀ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e₀).const_add x
  have h_fd : HasFDerivAt f (fderiv ℝ f x) ((fun s : ℝ => x + s • e₀) 0) := by
    simpa using f.differentiableAt.hasFDerivAt
  have h1 : HasDerivWithinAt (fun s : ℝ => f (x + s • e₀)) (fderiv ℝ f x e₀) (Set.Iic 0) 0 := by
    have h_comp := h_fd.comp_hasDerivAt 0 h_path
    exact ((by simpa [Function.comp_def] using h_comp : HasDerivAt _ _ _)).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun s : ℝ => f (x + s • e₀)) 0 (Set.Iic 0) 0 :=
    (hasDerivWithinAt_const 0 _ (0 : ℂ)).congr h_vanish (h_vanish 0 Set.self_mem_Iic)
  have e1 := h1.derivWithin (uniqueDiffWithinAt_Iic 0)
  have e2 := h2.derivWithin (uniqueDiffWithinAt_Iic 0)
  rw [← e1, e2]

/-- **Order-`N` boundary-vanishing bound with spatial decay.**  A Schwartz function vanishing
    on the half-space `{x₀ ≤ 0}` satisfies `‖f(t, x̄)‖ ≤ C · tᴺ / (1 + ‖x̄‖)^d` for every `N`.
    The case `N = 1` is the fundamental-theorem estimate; the general case follows by
    induction, applying the inductive bound to the time derivative of `f` (again a Schwartz
    function vanishing on the half-space) and integrating along the time direction. -/
theorem schwartz_vanishing_pow_decay (N : ℕ) (f : SchwartzTestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (_ : 0 < t) (x_sp : SpatialCoords d),
      ‖f (spacetimeOfTimeSpace t x_sp)‖ ≤ C * t ^ N / (1 + ‖x_sp‖) ^ d := by
  induction N generalizing f with
  | zero =>
      obtain ⟨C, hC_pos, hC⟩ := schwartz_pointwise_decay_bound f
      refine ⟨C, hC_pos, fun t ht x_sp => ?_⟩
      have h1x : (0 : ℝ) < 1 + ‖x_sp‖ := by linarith [norm_nonneg x_sp]
      have h_norm_ge := spacetimeOfTimeSpace_norm_ge t x_sp
      have h_mono : (1 + ‖x_sp‖) ^ d ≤ (1 + ‖spacetimeOfTimeSpace t x_sp‖) ^ d := by
        apply pow_le_pow_left₀ (by linarith) (by linarith)
      calc ‖f (spacetimeOfTimeSpace t x_sp)‖
          ≤ C / (1 + ‖spacetimeOfTimeSpace t x_sp‖) ^ d := hC _
        _ ≤ C / (1 + ‖x_sp‖) ^ d := by
            apply div_le_div_of_nonneg_left hC_pos.le (pow_pos h1x d) h_mono
        _ = C * t ^ 0 / (1 + ‖x_sp‖) ^ d := by rw [pow_zero, mul_one]
  | succ N ih =>
      set e₀ : SpaceTime d := EuclideanSpace.single (0 : Fin d) (1 : ℝ) with he₀
      set g : SchwartzTestFunctionℂ d := LineDeriv.lineDerivOp e₀ f with hg_def
      have hg_apply : ∀ y : SpaceTime d, g y = fderiv ℝ f y e₀ := fun y => rfl
      have hg_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → g x = 0 := fun x hx => by
        rw [hg_apply x, he₀]
        exact schwartz_vanishing_fderiv_time f hf_supp x hx
      obtain ⟨C, hC_pos, hC⟩ := ih g hg_supp
      refine ⟨C / ((N : ℝ) + 1), by positivity, fun t ht x_sp => ?_⟩
      have h1x : (0 : ℝ) < 1 + ‖x_sp‖ := by linarith [norm_nonneg x_sp]
      have hP : (0 : ℝ) < (1 + ‖x_sp‖) ^ d := pow_pos h1x d
      set K : ℝ := C / (1 + ‖x_sp‖) ^ d with hK_def
      have hK_pos : 0 < K := div_pos hC_pos hP
      set F : ℝ → ℂ := fun s => f (spacetimeOfTimeSpace s x_sp) with hF_def
      have h_path_eq : (fun r : ℝ => spacetimeOfTimeSpace (d := d) r x_sp) =
          (fun r : ℝ => spacetimeOfTimeSpace 0 x_sp + r • e₀) := by
        funext r
        rw [spacetimeOfTimeSpace_decompose r x_sp, spacetimeOfTimeSpace_eq_smul_single, add_comm,
          he₀]
      have h_path_cont : Continuous (fun r : ℝ => spacetimeOfTimeSpace (d := d) r x_sp) := by
        rw [h_path_eq]
        exact continuous_const.add (continuous_id.smul continuous_const)
      have h_F_cont : ContinuousOn F (Set.Icc 0 t) :=
        (f.continuous.comp h_path_cont).continuousOn
      have h_F_deriv : ∀ s : ℝ, HasDerivAt F (g (spacetimeOfTimeSpace s x_sp)) s := by
        intro s
        have h_path : HasDerivAt (fun r : ℝ => spacetimeOfTimeSpace (d := d) r x_sp) e₀ s := by
          rw [h_path_eq]
          simpa using ((hasDerivAt_id s).smul_const e₀).const_add (spacetimeOfTimeSpace 0 x_sp)
        have h_fd : HasFDerivAt f (fderiv ℝ f (spacetimeOfTimeSpace s x_sp))
            (spacetimeOfTimeSpace s x_sp) := f.differentiableAt.hasFDerivAt
        have h_comp := h_fd.comp_hasDerivAt s h_path
        simpa [Function.comp_def, hg_apply] using h_comp
      have h_F0 : F 0 = 0 := hf_supp _ (le_of_eq (spacetimeOfTimeSpace_time 0 x_sp))
      have h_B : ∀ s : ℝ,
          HasDerivAt (fun r : ℝ => K * r ^ (N + 1) / ((N : ℝ) + 1)) (K * s ^ N) s := by
        intro s
        have h1 : HasDerivAt (fun r : ℝ => r ^ (N + 1)) (((N : ℝ) + 1) * s ^ N) s := by
          simpa using hasDerivAt_pow (N + 1) s
        have h2 := (h1.const_mul K).div_const ((N : ℝ) + 1)
        have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
        have hval : K * (((N : ℝ) + 1) * s ^ N) / ((N : ℝ) + 1) = K * s ^ N := by
          rw [show K * (((N : ℝ) + 1) * s ^ N) / ((N : ℝ) + 1)
              = K * s ^ N * (((N : ℝ) + 1) / ((N : ℝ) + 1)) from by ring,
            div_self hN1, mul_one]
        exact hval ▸ h2
      have h_bound : ∀ s ∈ Set.Ico (0 : ℝ) t, ‖g (spacetimeOfTimeSpace s x_sp)‖ ≤ K * s ^ N := by
        intro s hs
        rcases eq_or_lt_of_le hs.1 with hs0 | hs0
        · rw [← hs0, hg_supp _ (le_of_eq (spacetimeOfTimeSpace_time 0 x_sp)), norm_zero]
          exact mul_nonneg hK_pos.le (pow_nonneg le_rfl N)
        · calc ‖g (spacetimeOfTimeSpace s x_sp)‖
              ≤ C * s ^ N / (1 + ‖x_sp‖) ^ d := hC s hs0 x_sp
            _ = K * s ^ N := by rw [hK_def]; ring
      have h_main := image_norm_le_of_norm_deriv_right_le_deriv_boundary
        (f' := fun s => g (spacetimeOfTimeSpace s x_sp))
        (B := fun r : ℝ => K * r ^ (N + 1) / ((N : ℝ) + 1)) (B' := fun s => K * s ^ N)
        h_F_cont (fun s _ => (h_F_deriv s).hasDerivWithinAt)
        (by simp [h_F0]) h_B h_bound (Set.right_mem_Icc.mpr ht.le)
      calc ‖f (spacetimeOfTimeSpace t x_sp)‖ = ‖F t‖ := rfl
        _ ≤ K * t ^ (N + 1) / ((N : ℝ) + 1) := h_main
        _ = C / ((N : ℝ) + 1) * t ^ (N + 1) / (1 + ‖x_sp‖) ^ d := by
            rw [hK_def]
            field_simp

/-- **Order-`N` boundary-vanishing bound (global form).**  A Schwartz function vanishing on
    the half-space `{x₀ ≤ 0}` satisfies `‖f x‖ ≤ C · x₀ᴺ` for `x₀ > 0`. -/
theorem schwartz_vanishing_pow_bound (N : ℕ) (f : SchwartzTestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : SpaceTime d, 0 < x 0 → ‖f x‖ ≤ C * (x 0) ^ N := by
  obtain ⟨C, hC_pos, hC⟩ := schwartz_vanishing_pow_decay N f hf_supp
  refine ⟨C, hC_pos, fun x hx => ?_⟩
  have h_pow : (1 : ℝ) ≤ (1 + ‖spatialPart x‖) ^ d :=
    one_le_pow₀ (by linarith [norm_nonneg (spatialPart x)])
  have h_bd := hC (x 0) hx (spatialPart x)
  rw [spacetimeOfTimeSpace_spatialPart x] at h_bd
  calc ‖f x‖ ≤ C * (x 0) ^ N / (1 + ‖spatialPart x‖) ^ d := h_bd
    _ ≤ C * (x 0) ^ N / 1 := by
        apply div_le_div_of_nonneg_left (by positivity) one_pos h_pow
    _ = C * (x 0) ^ N := div_one _

/-- **Order-`N` spatial-integral bound**: for a Schwartz function vanishing on `{x₀ ≤ 0}`,
    `∫_{ℝ^{d-1}} ‖f(t, x̄)‖ dx̄ ≤ C · tᴺ` for `t > 0`.  Integrates the pointwise order-`N`
    bound against the integrable spatial decay `(1 + ‖x̄‖)⁻ᵈ`. -/
theorem spatialNormIntegral_pow_bound (N : ℕ) (f : SchwartzTestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → spatialNormIntegral f t ≤ C * t ^ N := by
  obtain ⟨C_pt, hC_pt_pos, h_pt_bound⟩ := schwartz_vanishing_pow_decay N f hf_supp
  have h_decay_int := polynomial_decay_integrable_spatial (d := d)
  let K := ∫ x : SpatialCoords d, 1 / (1 + ‖x‖) ^ d
  have hK_nonneg : 0 ≤ K := integral_nonneg (fun x => by positivity)
  refine ⟨C_pt * (K + 1), mul_pos hC_pt_pos (by linarith), fun t ht => ?_⟩
  have h_pointwise : ∀ x : SpatialCoords d,
      ‖f (spacetimeOfTimeSpace t x)‖ ≤ C_pt * t ^ N / (1 + ‖x‖) ^ d := fun x =>
    h_pt_bound t ht x
  have h_bound_int :
      Integrable (fun x : SpatialCoords d => C_pt * t ^ N / (1 + ‖x‖) ^ d) volume := by
    have h_eq : (fun x : SpatialCoords d => C_pt * t ^ N / (1 + ‖x‖) ^ d) =
        (fun x : SpatialCoords d => (C_pt * t ^ N) * (1 / (1 + ‖x‖) ^ d)) := by
      ext x; ring
    rw [h_eq]
    exact h_decay_int.const_mul (C_pt * t ^ N)
  have h_mono := integral_mono_of_nonneg
    (f := fun x : SpatialCoords d => ‖f (spacetimeOfTimeSpace t x)‖)
    (g := fun x : SpatialCoords d => C_pt * t ^ N / (1 + ‖x‖) ^ d)
    (ae_of_all _ fun x => norm_nonneg _) h_bound_int (ae_of_all _ h_pointwise)
  have h_factor : ∫ x : SpatialCoords d, C_pt * t ^ N / (1 + ‖x‖) ^ d = C_pt * t ^ N * K := by
    have h_eq : (fun x : SpatialCoords d => C_pt * t ^ N / (1 + ‖x‖) ^ d) =
        (fun x : SpatialCoords d => (C_pt * t ^ N) * (1 / (1 + ‖x‖) ^ d)) := by ext x; ring
    rw [h_eq]
    simp only [← smul_eq_mul, integral_smul]
    rfl
  calc spatialNormIntegral f t
      = ∫ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖ := rfl
    _ ≤ ∫ x : SpatialCoords d, C_pt * t ^ N / (1 + ‖x‖) ^ d := h_mono
    _ = C_pt * t ^ N * K := h_factor
    _ ≤ C_pt * t ^ N * (K + 1) := by nlinarith [mul_pos hC_pt_pos (pow_pos ht N)]
    _ = C_pt * (K + 1) * t ^ N := by ring

end TimeSlice

