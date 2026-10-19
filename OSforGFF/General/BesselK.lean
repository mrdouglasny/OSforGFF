/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
module

public import OSforGFF.General.BesselK0
public import OSforGFF.General.BesselFunction
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The modified Bessel function `K_ν` of arbitrary order and the master Schwinger identity

The proper-time (Schwinger) evaluation underlying the free covariance is, in every dimension `d`,
a single integral of the shape `∫₀^∞ t^{ν-1} e^{-m²t - r²/(4t)} dt` with `ν = 1 - d/2`. This file
introduces the modified Bessel function of the second kind of arbitrary order through its cosh
integral representation

`K_ν(z) = ∫₀^∞ e^{-z cosh t} · cosh(ν t) dt`,

and proves the **master Schwinger identity**

`∫₀^∞ t^{ν-1} e^{-m²t - r²/(4t)} dt = 2 (r/(2m))^ν · K_ν(m r)`

by the change of variables `t = (r/(2m)) eᵘ` followed by a symmetrization of the resulting full-line
integral. The order-zero and order-one instances (`besselK0`, `besselK1`) coincide with `K_0` and
`K_1`, so the two per-order Schwinger evaluations used by the two- and four-dimensional instances
are recovered as corollaries, and the elementary half-integer value
`K_{1/2}(z) = √(π/(2z)) · e^{-z}` supplies the three-dimensional (Yukawa) evaluation.
-/

@[expose] public section

open MeasureTheory Set Filter Real Topology Asymptotics intervalIntegral

noncomputable section

/-- The modified Bessel function of the second kind of order `ν`,
    `K_ν(z) = ∫₀^∞ e^{-z cosh t} · cosh(ν t) dt`. -/
def besselK (ν z : ℝ) : ℝ := ∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh (ν * t)

/-- `K_0` is the order-zero cosh integral `besselK0`. -/
lemma besselK_zero (z : ℝ) : besselK 0 z = besselK0 z := by
  unfold besselK besselK0
  refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
  rw [zero_mul, Real.cosh_zero, mul_one]

/-- `K_1` is the order-one cosh integral `besselK1`. -/
lemma besselK_one (z : ℝ) : besselK 1 z = besselK1 z := by
  unfold besselK besselK1
  refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
  rw [one_mul]

/-- `K_ν` is even in the order: `K_{-ν} = K_ν` (because `cosh` is even). -/
lemma besselK_neg (ν z : ℝ) : besselK (-ν) z = besselK ν z := by
  unfold besselK
  refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
  rw [show (-ν) * t = -(ν * t) by ring, Real.cosh_neg]

/-- `cosh t ≥ 1 + t²/2` for all `t`. -/
private lemma cosh_ge_one_add_sq_div_two (t : ℝ) : 1 + t ^ 2 / 2 ≤ cosh t := by
  rw [← Real.cosh_abs t]
  set s := |t|; have hs : 0 ≤ s := abs_nonneg t
  have key : cosh s = 1 + 2 * sinh (s / 2) ^ 2 := by
    rw [show s = 2 * (s / 2) from by ring, Real.cosh_two_mul, Real.cosh_sq']; ring_nf
  rw [key]
  have h_sinh : s / 2 ≤ sinh (s / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h_sq : (s / 2) ^ 2 ≤ sinh (s / 2) ^ 2 :=
    sq_le_sq' (by linarith [Real.sinh_nonneg_iff.mpr (by linarith : 0 ≤ s / 2)]) h_sinh
  nlinarith [sq_abs t]

/-- `exp(-z cosh t) ≤ exp(-z) · exp(-(z/2) t²)` for `z > 0` (Gaussian domination). -/
private lemma exp_neg_cosh_le_gaussian (z t : ℝ) (hz : 0 < z) :
    exp (-z * cosh t) ≤ exp (-z) * exp (-(z / 2) * t ^ 2) := by
  rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith [cosh_ge_one_add_sq_div_two t])

/-- A shifted Gaussian `exp(b t - a t²)` is integrable on `ℝ` for `a > 0`. -/
private lemma integrable_exp_linear_sub_sq (a b : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => exp (b * t - a * t ^ 2)) := by
  have hcomp : (fun t : ℝ => exp (b * t - a * t ^ 2))
      = fun t => exp (b ^ 2 / (4 * a)) * exp (-a * (t - b / (2 * a)) ^ 2) := by
    funext t; rw [← exp_add]; congr 1; field_simp; ring
  rw [hcomp]
  apply Integrable.const_mul
  have := (integrable_exp_neg_mul_sq ha).comp_sub_right (b / (2 * a))
  simpa [mul_comm] using this

/-- The symmetrization integrand `exp(ν u) · exp(-z cosh u)` is integrable on `ℝ` for `z > 0`. -/
private lemma symm_integrand_integrable (ν z : ℝ) (hz : 0 < z) :
    Integrable (fun u : ℝ => exp (ν * u) * exp (-z * cosh u)) := by
  apply Integrable.mono' (g := fun u => exp (-z) * exp (ν * u - (z / 2) * u ^ 2))
  · exact (integrable_exp_linear_sub_sq (z / 2) ν (by linarith)).const_mul _
  · exact ((continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_exp.comp (continuous_const.mul continuous_cosh))).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (exp_pos _) (exp_pos _))]
    calc exp (ν * u) * exp (-z * cosh u)
        ≤ exp (ν * u) * (exp (-z) * exp (-(z / 2) * u ^ 2)) :=
          mul_le_mul_of_nonneg_left (exp_neg_cosh_le_gaussian z u hz) (exp_pos _).le
      _ = exp (-z) * exp (ν * u - (z / 2) * u ^ 2) := by
          rw [← exp_add, ← exp_add, ← exp_add]; congr 1; ring

/-- Symmetrization: `∫_ℝ exp(ν u) exp(-z cosh u) du = 2 · K_ν(z)`, the even part in `u` giving
    twice the half-line cosh integral. -/
private lemma bessel_symmetry_gen (ν z : ℝ) (hz : 0 < z) :
    ∫ u : ℝ, exp (ν * u) * exp (-z * cosh u) = 2 * besselK ν z := by
  have hpos := symm_integrand_integrable ν z hz
  have hneg := symm_integrand_integrable (-ν) z hz
  have hf_Ioi : IntegrableOn (fun u => exp (ν * u) * exp (-z * cosh u)) (Ioi 0) := hpos.integrableOn
  have hf_Iic : IntegrableOn (fun u => exp (ν * u) * exp (-z * cosh u)) (Iic 0) := hpos.integrableOn
  have hg_Ioi : IntegrableOn (fun u => exp (-(ν * u)) * exp (-z * cosh u)) (Ioi 0) := by
    refine hneg.integrableOn.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [neg_mul]
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hf_Iic hf_Ioi]
  have h_neg_part : ∫ u in Iic 0, exp (ν * u) * exp (-z * cosh u) =
      ∫ u in Ioi 0, exp (-(ν * u)) * exp (-z * cosh u) := by
    have h := integral_comp_neg_Iic (f := fun u => exp (-(ν * u)) * exp (-z * cosh u)) 0
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic (fun u _ => ?_)
    rw [cosh_neg, mul_neg, neg_neg]
  rw [h_neg_part, ← MeasureTheory.integral_add hg_Ioi hf_Ioi]
  have h_combine : ∫ u in Ioi 0,
        (exp (-(ν * u)) * exp (-z * cosh u) + exp (ν * u) * exp (-z * cosh u)) =
      ∫ u in Ioi 0, 2 * cosh (ν * u) * exp (-z * cosh u) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [Real.cosh_eq (ν * u)]; ring
  have hbk : (2 : ℝ) * besselK ν z = ∫ u in Ioi 0, 2 * cosh (ν * u) * exp (-z * cosh u) := by
    unfold besselK
    rw [integral_Ici_eq_integral_Ioi, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    ring
  rw [h_combine, hbk]

/-- **Master Schwinger identity.** For `m, r > 0` and any order `ν`,
    `∫₀^∞ t^{ν-1} e^{-m²t - r²/(4t)} dt = 2 (r/(2m))^ν · K_ν(m r)`.
    Proven by the substitution `t = (r/(2m)) eᵘ`, which turns the integrand into
    `(r/(2m))^ν e^{ν u} e^{-m r cosh u}`, and the symmetrization `bessel_symmetry_gen`. -/
theorem schwingerIntegral_eq_besselK (ν m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, t ^ (ν - 1) * exp (-m ^ 2 * t - r ^ 2 / (4 * t)) =
    2 * (r / (2 * m)) ^ ν * besselK ν (m * r) := by
  set c := r / (2 * m) with hc_def
  have hc : 0 < c := by positivity
  set z := m * r with hz_def
  have hz : 0 < z := mul_pos hm hr
  set g : ℝ → ℝ := fun t => t ^ (ν - 1) * exp (-m ^ 2 * t - r ^ 2 / (4 * t)) with hg_def
  have h_cov : ∫ t in Ioi 0, g t = ∫ u, (c * exp u) * g (c * exp u) := by
    let φ := fun u => c * exp u
    have hφ_mono : StrictMono φ := fun a b hab => mul_lt_mul_of_pos_left (exp_lt_exp.mpr hab) hc
    have hφ_surj : φ '' univ = Ioi 0 := by
      ext t; simp only [mem_image, mem_univ, true_and, mem_Ioi, φ]
      constructor
      · rintro ⟨u, rfl⟩; exact mul_pos hc (exp_pos u)
      · intro ht; exact ⟨Real.log (t / c), by rw [exp_log (by positivity)]; field_simp⟩
    have hφ_deriv : ∀ u ∈ univ, HasDerivWithinAt φ (c * exp u) univ u :=
      fun u _ => ((hasDerivAt_exp u).const_mul c).hasDerivWithinAt
    calc ∫ t in Ioi 0, g t
        = ∫ t in φ '' univ, g t := by rw [hφ_surj]
      _ = ∫ u in univ, (c * exp u) • g (φ u) :=
          integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
            hφ_deriv (hφ_mono.monotone.monotoneOn univ) g
      _ = ∫ u, (c * exp u) * g (c * exp u) := by rw [setIntegral_univ]; simp only [smul_eq_mul, φ]
  have h_transform : ∀ u : ℝ, (c * exp u) * g (c * exp u) =
      c ^ ν * (exp (ν * u) * exp (-z * cosh u)) := by
    intro u
    have hce : (0 : ℝ) < c * exp u := mul_pos hc (exp_pos u)
    have he : exp u ≠ 0 := (exp_pos u).ne'
    have hpow : (c * exp u) * (c * exp u) ^ (ν - 1) = c ^ ν * exp (ν * u) := by
      have h1 : (c * exp u) * (c * exp u) ^ (ν - 1) = (c * exp u) ^ ν := by
        rw [Real.rpow_sub hce, Real.rpow_one]; field_simp
      rw [h1, Real.mul_rpow hc.le (exp_pos u).le, ← Real.exp_mul, mul_comm u ν]
    have hsum : m ^ 2 * (c * exp u) + r ^ 2 / (4 * (c * exp u)) = z * cosh u := by
      simp only [hc_def, hz_def]
      have h1 : exp u * exp (-u) = 1 := by rw [exp_neg]; exact mul_inv_cancel₀ he
      field_simp
      rw [Real.cosh_eq]; ring_nf; rw [h1]; ring
    have hexp : exp (-m ^ 2 * (c * exp u) - r ^ 2 / (4 * (c * exp u))) = exp (-z * cosh u) := by
      congr 1
      rw [show -m ^ 2 * (c * exp u) - r ^ 2 / (4 * (c * exp u))
            = -(m ^ 2 * (c * exp u) + r ^ 2 / (4 * (c * exp u))) by ring, hsum]
      ring
    simp only [hg_def]
    calc (c * exp u) *
          ((c * exp u) ^ (ν - 1) * exp (-m ^ 2 * (c * exp u) - r ^ 2 / (4 * (c * exp u))))
        = ((c * exp u) * (c * exp u) ^ (ν - 1)) *
            exp (-m ^ 2 * (c * exp u) - r ^ 2 / (4 * (c * exp u))) := by ring
      _ = (c ^ ν * exp (ν * u)) * exp (-z * cosh u) := by rw [hpow, hexp]
      _ = c ^ ν * (exp (ν * u) * exp (-z * cosh u)) := by ring
  rw [h_cov, MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_transform),
      MeasureTheory.integral_const_mul, bessel_symmetry_gen ν z hz]
  ring

/-- Half-integer Bessel in closed form: `K_{1/2}(z) = √(π/(2z)) · e^{-z}`
    (the substitution `u = sinh(t/2)` reduces the cosh integral to a Gaussian). -/
lemma besselK_half (z : ℝ) :
    besselK (1 / 2) z = Real.sqrt (Real.pi / (2 * z)) * exp (-z) := by
  have hint : besselK (1 / 2) z =
      exp (-z) * ∫ t in Ici 0, exp (-(2 * z) * sinh (t / 2) ^ 2) * cosh (t / 2) := by
    unfold besselK
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    have hcosh : cosh t = 1 + 2 * sinh (t / 2) ^ 2 := by
      rw [show t = 2 * (t / 2) from by ring, Real.cosh_two_mul, Real.cosh_sq']; ring
    rw [show (1 / 2 : ℝ) * t = t / 2 by ring, hcosh,
        show -z * (1 + 2 * sinh (t / 2) ^ 2) = -z + -(2 * z) * sinh (t / 2) ^ 2 by ring, Real.exp_add]
    ring
  have hcov : ∫ t in Ici 0, exp (-(2 * z) * sinh (t / 2) ^ 2) * cosh (t / 2) =
      2 * ∫ u in Ici 0, exp (-(2 * z) * u ^ 2) := by
    have hderiv : ∀ t ∈ Ici (0 : ℝ),
        HasDerivWithinAt (fun t => sinh (t / 2)) (cosh (t / 2) / 2) (Ici 0) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := (hasDerivAt_id t).div_const 2
      have h2 : HasDerivAt (fun t : ℝ => sinh (t / 2)) (cosh (t / 2) * (1 / 2)) t := by
        simpa [Function.comp_def] using (Real.hasDerivAt_sinh (t / 2)).comp t h1
      rw [show cosh (t / 2) / 2 = cosh (t / 2) * (1 / 2) by ring]
      exact h2.hasDerivWithinAt
    have hmono : MonotoneOn (fun t => sinh (t / 2)) (Ici 0) :=
      fun a _ b _ hab => Real.sinh_le_sinh.mpr (by linarith)
    have himg : (fun t => sinh (t / 2)) '' Ici 0 = Ici 0 := by
      ext y; simp only [mem_image, mem_Ici]
      constructor
      · rintro ⟨t, ht, rfl⟩; exact Real.sinh_nonneg_iff.mpr (by linarith)
      · intro hy
        refine ⟨2 * Real.arsinh y, ?_, ?_⟩
        · have : 0 ≤ Real.arsinh y := Real.arsinh_nonneg_iff.mpr hy
          linarith
        · rw [show 2 * Real.arsinh y / 2 = Real.arsinh y by ring, Real.sinh_arsinh]
    have h := integral_image_eq_integral_deriv_smul_of_monotoneOn (F := ℝ)
      measurableSet_Ici hderiv hmono (fun u => exp (-(2 * z) * u ^ 2))
    rw [himg] at h
    rw [h, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici (fun t _ => ?_)
    simp only [smul_eq_mul]; ring
  rw [hint, hcov, integral_Ici_eq_integral_Ioi, integral_gaussian_Ioi]
  ring

/-- The order-zero Schwinger evaluation (`ν = 0`), recovering the two-dimensional identity
    `∫₀^∞ (1/t) e^{-m²t - r²/(4t)} dt = 2 K_0(m r)`. -/
theorem schwingerIntegral_eq_besselK0 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t) * exp (-m ^ 2 * t - r ^ 2 / (4 * t)) = 2 * besselK0 (m * r) := by
  have h := schwingerIntegral_eq_besselK 0 m r hm hr
  rw [besselK_zero, Real.rpow_zero, mul_one] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [show (0 : ℝ) - 1 = -1 by norm_num, Real.rpow_neg_one, one_div]

/-- The order-one Schwinger evaluation (`ν = -1`, using evenness), recovering the four-dimensional
    identity `∫₀^∞ (1/t²) e^{-m²t - r²/(4t)} dt = (4m/r) K_1(m r)`. -/
theorem schwingerIntegral_eq_besselK1 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t ^ 2) * exp (-m ^ 2 * t - r ^ 2 / (4 * t)) = 4 * m / r * besselK1 (m * r) := by
  have h := schwingerIntegral_eq_besselK (-1) m r hm hr
  rw [besselK_neg, besselK_one] at h
  have hconst : 2 * (r / (2 * m)) ^ (-1 : ℝ) = 4 * m / r := by
    rw [Real.rpow_neg_one, inv_div]; field_simp; ring
  rw [hconst] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [show (-1 : ℝ) - 1 = -(2 : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_two, one_div]

end
