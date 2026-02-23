import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import OSforGFF.NuclearSpace.PhysHermiteGaussL2Basis
import OSforGFF.NuclearSpace.PhysHermiteSchwartz

/-!
# Completeness of harmonic-oscillator Hermite functions in `L²(ℝ)`

We transport the Gaussian-weight completeness of physicists' Hermite polynomials (proved in
`PhysHermiteGaussL2Basis.lean`) to the usual Lebesgue `L²(ℝ)` completeness of the harmonic-oscillator
eigenfunctions

`x ↦ physHermite n (x/ξ) * exp (-x^2 / (2 ξ^2))`.

This file provides the 1D analytic core needed later for spacetime (`ℝ⁴`) completeness and Parseval
identities for the spacetime coefficient map.
-/

open scoped BigOperators ENNReal RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory

namespace HarmonicOscillator

/-! ## The normalized 1D eigenfunctions as functions and as `L²` elements -/

/-- The squared `L²`-norm constant of the unnormalized 1D eigenfunction `eigenfunctionReal ξ n`. -/
noncomputable def normConstReal (ξ : ℝ) (n : ℕ) : ℝ :=
  |ξ| * (↑n.factorial * 2 ^ n * √Real.pi)

@[simp] lemma normConstReal_def (ξ : ℝ) (n : ℕ) :
    normConstReal ξ n = |ξ| * (↑n.factorial * 2 ^ n * √Real.pi) := rfl

lemma normConstReal_pos (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) : 0 < normConstReal ξ n := by
  have hξ' : 0 < |ξ| := abs_pos.2 hξ
  have hfac : 0 < (↑n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpow : 0 < (2 : ℝ) ^ n := by
    exact pow_pos (by norm_num : (0 : ℝ) < 2) n
  have hpi : 0 < (√Real.pi : ℝ) := by
    simpa using Real.sqrt_pos.2 Real.pi_pos
  have : 0 < (↑n.factorial * 2 ^ n * √Real.pi : ℝ) := by
    exact mul_pos (mul_pos hfac hpow) hpi
  simpa [normConstReal, mul_assoc] using mul_pos hξ' this

/-- The normalized 1D harmonic-oscillator eigenfunction as a plain function. -/
noncomputable def normalizedEigenfunctionReal (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt (normConstReal ξ n))⁻¹ * eigenfunctionReal ξ n x

@[simp] lemma normalizedEigenfunctionReal_def (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    normalizedEigenfunctionReal ξ hξ n x =
      (Real.sqrt (normConstReal ξ n))⁻¹ * eigenfunctionReal ξ n x := rfl

lemma continuous_eigenfunctionReal (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Continuous (eigenfunctionReal ξ n) := by
  -- `eigenfunctionRealSchwartz` is `C^∞`, hence continuous.
  have hcont : Continuous (fun x : ℝ => eigenfunctionRealSchwartz ξ hξ n x) :=
    (eigenfunctionRealSchwartz ξ hξ n).smooth'.continuous
  simpa [eigenfunctionRealSchwartz_apply] using hcont

lemma aestronglyMeasurable_eigenfunctionReal (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    AEStronglyMeasurable (eigenfunctionReal ξ n) (volume : Measure ℝ) := by
  exact (continuous_eigenfunctionReal (ξ := ξ) (hξ := hξ) n).aestronglyMeasurable

lemma integrable_eigenfunctionReal_sq (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Integrable (fun x : ℝ => (eigenfunctionReal ξ n x) ^ 2) (volume : Measure ℝ) := by
  -- if not integrable, the integral is `0`, contradicting the explicit positive value
  by_contra h
  have h0 :
      (∫ x : ℝ, eigenfunctionReal ξ n x * eigenfunctionReal ξ n x ∂(volume : Measure ℝ)) = 0 := by
    have : ¬Integrable (fun x : ℝ => eigenfunctionReal ξ n x * eigenfunctionReal ξ n x)
        (volume : Measure ℝ) := by
      simpa [pow_two] using h
    exact MeasureTheory.integral_undef this
  have hpos :
      0 < (∫ x : ℝ, eigenfunctionReal ξ n x * eigenfunctionReal ξ n x) := by
    -- use the closed form from `PhysHermite`
    have hn :
        (∫ x : ℝ, eigenfunctionReal ξ n x * eigenfunctionReal ξ n x) =
          |ξ| * (↑n.factorial * 2 ^ n * √Real.pi) := by
      simpa [smul_eq_mul, normConstReal] using (eigenfunctionReal_norm (ξ := ξ) n)
    rw [hn]
    exact normConstReal_pos (ξ := ξ) hξ n
  exact (ne_of_gt hpos) h0

lemma memLp_eigenfunctionReal (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    MemLp (eigenfunctionReal ξ n) 2 (volume : Measure ℝ) := by
  have hmeas :
      AEStronglyMeasurable (eigenfunctionReal ξ n) (volume : Measure ℝ) :=
    aestronglyMeasurable_eigenfunctionReal (ξ := ξ) (hξ := hξ) n
  have hint :
      Integrable (fun x : ℝ => (eigenfunctionReal ξ n x) ^ 2) (volume : Measure ℝ) :=
    integrable_eigenfunctionReal_sq (ξ := ξ) (hξ := hξ) n
  exact (MeasureTheory.memLp_two_iff_integrable_sq (μ := (volume : Measure ℝ)) hmeas).2 hint

/-- The unnormalized eigenfunction as an element of `L²(ℝ)` (Lebesgue). -/
noncomputable def eigenfunctionRealL2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    ℝ →₂[(volume : Measure ℝ)] ℝ :=
  (memLp_eigenfunctionReal (ξ := ξ) hξ n).toLp (eigenfunctionReal ξ n)

/-- The normalized eigenfunction as an element of `L²(ℝ)` (Lebesgue). -/
noncomputable def normalizedEigenfunctionRealL2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    ℝ →₂[(volume : Measure ℝ)] ℝ :=
  (Real.sqrt (normConstReal ξ n))⁻¹ • eigenfunctionRealL2 (ξ := ξ) hξ n

/-! ## Completeness in `L²(ℝ)` via the Gaussian-weight completeness -/

private lemma exp_sq_half_ne_zero (x : ℝ) : Real.exp (x ^ 2 / 2) ≠ 0 := by
  exact (Real.exp_pos _).ne'

private lemma exp_neg_sq_mul_exp_sq_half_mul_exp_sq_half (y : ℝ) :
    Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2)) = 1 := by
  -- `exp(-y^2) * exp(y^2/2) * exp(y^2/2) = exp(0) = 1`
  have hsum : y ^ 2 / 2 + y ^ 2 / 2 = y ^ 2 := by ring
  calc
    Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2))
        = Real.exp (-y ^ 2) * Real.exp (y ^ 2 / 2 + y ^ 2 / 2) := by
            simp [← Real.exp_add, mul_assoc]
    _ = Real.exp (-y ^ 2) * Real.exp (y ^ 2) := by simp [hsum]
    _ = Real.exp (-y ^ 2 + y ^ 2) := by simp [← Real.exp_add]
    _ = Real.exp 0 := by simp
    _ = 1 := by simp

private lemma exp_neg_sq_mul_exp_sq_half (y : ℝ) :
    Real.exp (-y ^ 2) * Real.exp (y ^ 2 / 2) = Real.exp (-y ^ 2 / 2) := by
  -- `exp(-y^2) * exp(y^2/2) = exp(-y^2 + y^2/2)`
  calc
    Real.exp (-y ^ 2) * Real.exp (y ^ 2 / 2)
        = Real.exp (-y ^ 2 + y ^ 2 / 2) := by simp [← Real.exp_add]
    _ = Real.exp (-y ^ 2 / 2) := by ring_nf

private lemma exp_neg_sq_mul_exp_sq_half_mul (y a : ℝ) :
    Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * a) = Real.exp (-y ^ 2 / 2) * a := by
  -- pull out the factor `a`
  calc
    Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * a)
        = (Real.exp (-y ^ 2) * Real.exp (y ^ 2 / 2)) * a := by ring_nf
    _ = Real.exp (-y ^ 2 / 2) * a := by simp [exp_neg_sq_mul_exp_sq_half]

private lemma ae_eq_zero_of_ae_comp_mul_left {ξ : ℝ} (hξ : ξ ≠ 0) {g : ℝ → ℝ}
    (h : (fun x : ℝ => g (ξ * x)) =ᵐ[(volume : Measure ℝ)] 0) :
    g =ᵐ[(volume : Measure ℝ)] 0 := by
  -- Use the scaling formula for Haar/Lebesgue measure: preimages under `x ↦ ξ • x` scale measure.
  have hpre :
      (volume : Measure ℝ) ((fun x : ℝ => ξ • x) ⁻¹' {y : ℝ | g y ≠ 0}) = 0 := by
    -- `h` says `g(ξ*x) = 0` a.e., i.e. the preimage of `{g ≠ 0}` is null.
    have : (∀ᵐ x : ℝ ∂(volume : Measure ℝ), g (ξ * x) = 0) := h
    have : (∀ᵐ x : ℝ ∂(volume : Measure ℝ), ¬ (g (ξ * x) ≠ 0)) := by
      filter_upwards [this] with x hx
      simpa [hx]
    -- rewrite the set and extract the null-set statement
    simpa [Set.preimage, smul_eq_mul] using (ae_iff.1 this)
  -- Convert the preimage-null statement to `volume {g ≠ 0} = 0`.
  have hscale :
      (volume : Measure ℝ) ((fun x : ℝ => ξ • x) ⁻¹' {y : ℝ | g y ≠ 0}) =
        ENNReal.ofReal (abs (ξ ^ Module.finrank ℝ ℝ)⁻¹) *
          (volume : Measure ℝ) {y : ℝ | g y ≠ 0} := by
    simpa using
      (MeasureTheory.Measure.addHaar_preimage_smul (μ := (volume : Measure ℝ)) (E := ℝ) (r := ξ) hξ
        (s := {y : ℝ | g y ≠ 0}))
  have hconst_ne : ENNReal.ofReal (abs (ξ ^ Module.finrank ℝ ℝ)⁻¹) ≠ 0 := by
    -- In `ℝ`, `finrank = 1` and `ξ ≠ 0` gives a nonzero scaling constant.
    simp [Module.finrank_self, hξ]
  have : (volume : Measure ℝ) {y : ℝ | g y ≠ 0} = 0 := by
    have hmul :
        ENNReal.ofReal (abs (ξ ^ Module.finrank ℝ ℝ)⁻¹) *
            (volume : Measure ℝ) {y : ℝ | g y ≠ 0} = 0 := by
      exact hscale.symm.trans hpre
    exact (mul_eq_zero.mp hmul).resolve_left hconst_ne
  -- conclude `g = 0` a.e.
  refine (ae_iff.2 ?_)
  simpa [this]

/-- If `g ∈ L²(ℝ)` is orthogonal to all harmonic-oscillator eigenfunctions `eigenfunctionReal ξ n`,
then `g = 0` a.e. -/
theorem ae_eq_zero_of_forall_integral_eigenfunctionReal_eq_zero
    (ξ : ℝ) (hξ : ξ ≠ 0) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume : Measure ℝ))
    (horth : ∀ n : ℕ, ∫ x : ℝ, g x * eigenfunctionReal ξ n x = 0) :
    g =ᵐ[(volume : Measure ℝ)] 0 := by
  classical
  -- Define the transformed function living in the Gaussian-weight `L²`.
  let h : ℝ → ℝ := fun y => g (ξ * y) * Real.exp (y ^ 2 / 2)
  have hh_meas : AEStronglyMeasurable h (volume : Measure ℝ) := by
    have hq :
        MeasureTheory.Measure.QuasiMeasurePreserving (fun y : ℝ => ξ • y)
          (volume : Measure ℝ) (volume : Measure ℝ) :=
      MeasureTheory.Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (E := ℝ)
        (r := ξ) hξ
    have hmul : AEStronglyMeasurable (fun y : ℝ => g (ξ • y)) (volume : Measure ℝ) :=
      hg.1.comp_quasiMeasurePreserving hq
    -- rewrite `ξ • y` as `ξ * y`
    have hmul' : AEStronglyMeasurable (fun y : ℝ => g (ξ * y)) (volume : Measure ℝ) := by
      simpa [smul_eq_mul] using hmul
    exact hmul'.mul (by fun_prop)
  -- `h ∈ L²(gaussMeasure)` because the Gaussian density cancels the exponential factor.
  have hh_memLp : MemLp h 2 PhysHermiteGauss.gaussMeasure := by
    -- First, `g^2` integrable and scaling preserves integrability for Lebesgue/Haar.
    have hsq_int : Integrable (fun y : ℝ => (g (ξ * y)) ^ 2) (volume : Measure ℝ) := by
      have hg_sq : Integrable (fun x : ℝ => (g x) ^ 2) (volume : Measure ℝ) :=
        MeasureTheory.MemLp.integrable_sq hg
      have := (MeasureTheory.integrable_comp_smul_iff (μ := (volume : Measure ℝ))
        (f := fun x : ℝ => (g x) ^ 2) (hR := hξ)).2 hg_sq
      simpa [smul_eq_mul, mul_assoc] using this
    -- Now use `integrable_withDensity_iff` to transfer integrability to `gaussMeasure`.
    let ρ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-y ^ 2))
    have hρ_meas : Measurable ρ := by fun_prop
    have hρ_fin : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ρ y < ∞ := by
      exact ae_of_all _ (fun _ => by simp [ρ])
    have hh_meas_gauss : AEStronglyMeasurable h PhysHermiteGauss.gaussMeasure := by
      have hac :
          PhysHermiteGauss.gaussMeasure ≪ (volume : Measure ℝ) := by
        simpa [PhysHermiteGauss.gaussMeasure_def, ρ] using
          (MeasureTheory.withDensity_absolutelyContinuous (μ := (volume : Measure ℝ)) (f := ρ))
      exact AEStronglyMeasurable.mono_ac hac hh_meas
    have hsq_gauss : Integrable (fun y : ℝ => (h y) ^ 2) PhysHermiteGauss.gaussMeasure := by
      -- unfold `gaussMeasure` and use the integrability equivalence
      have hiff :
          Integrable (fun y : ℝ => (h y) ^ 2) ((volume : Measure ℝ).withDensity ρ) ↔
            Integrable (fun y : ℝ => (h y) ^ 2 * (ρ y).toReal) (volume : Measure ℝ) := by
        simpa using (MeasureTheory.integrable_withDensity_iff (μ := (volume : Measure ℝ))
          (f := ρ) hρ_meas hρ_fin (g := fun y : ℝ => (h y) ^ 2))
      -- simplify the weighted integrand pointwise
      have hpoint :
          (fun y : ℝ => (h y) ^ 2 * (ρ y).toReal) =
            fun y : ℝ => (g (ξ * y)) ^ 2 := by
        funext y
        have htoReal : (ρ y).toReal = Real.exp (-y ^ 2) := by
          simp [ρ, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
        -- expand `h` and cancel the Gaussian density
        -- `(g(ξ*y) * exp(y^2/2))^2 * exp(-y^2) = (g(ξ*y))^2`
        calc
          (h y) ^ 2 * (ρ y).toReal
              = (g (ξ * y) * Real.exp (y ^ 2 / 2)) ^ 2 * Real.exp (-y ^ 2) := by
                  simp [h, htoReal]
          _ = (g (ξ * y)) ^ 2 *
                (Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * Real.exp (y ^ 2 / 2))) := by
                  ring_nf
          _ = (g (ξ * y)) ^ 2 := by
                simp [exp_neg_sq_mul_exp_sq_half_mul_exp_sq_half]
      have : Integrable (fun y : ℝ => (h y) ^ 2 * (ρ y).toReal) (volume : Measure ℝ) := by
        simpa [hpoint] using hsq_int
      -- conclude
      have : Integrable (fun y : ℝ => (h y) ^ 2) ((volume : Measure ℝ).withDensity ρ) :=
        (hiff.2 this)
      simpa [PhysHermiteGauss.gaussMeasure_def, ρ] using this
    -- back to `MemLp` with `p=2`
    exact (MeasureTheory.memLp_two_iff_integrable_sq (μ := PhysHermiteGauss.gaussMeasure)
      (f := h) (hf := hh_meas_gauss)).2 hsq_gauss
  -- Orthogonality of `h` against all `physHermite` follows from the assumed orthogonality of `g`
  -- against `eigenfunctionReal`.
  have horth' : ∀ n : ℕ, ∫ y : ℝ, h y * physHermite n y ∂PhysHermiteGauss.gaussMeasure = 0 := by
    intro n
    -- Rewrite the integral against `gaussMeasure` as an integral on Lebesgue with density `exp(-y^2)`.
    let ρ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-y ^ 2))
    have hρ_meas : AEMeasurable ρ (volume : Measure ℝ) := by fun_prop
    have hρ_fin : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ρ y < ∞ := by
      exact ae_of_all _ (fun _ => by simp [ρ])
    have hwd :
        (∫ y : ℝ, h y * physHermite n y ∂(volume : Measure ℝ).withDensity ρ) =
          ∫ y : ℝ, ((ρ y).toReal : ℝ) • (h y * physHermite n y) ∂(volume : Measure ℝ) := by
      simpa using
        (integral_withDensity_eq_integral_toReal_smul₀ (μ := (volume : Measure ℝ)) (f := ρ)
          hρ_meas hρ_fin (g := fun y : ℝ => h y * physHermite n y))
    -- simplify the scalar action and identify the result with the change-of-variables form
    have htoReal : ∀ y : ℝ, (ρ y).toReal = Real.exp (-y ^ 2) := by
      intro y
      simp [ρ, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    -- Use the scaling lemma `integral_comp_mul_left` to rewrite the assumed orthogonality.
    -- Set `k(y) = g y * physHermite n (y/ξ) * gaussianHO ξ y`.
    let k : ℝ → ℝ := fun y => g y * physHermite n (y / ξ) * gaussianHO ξ y
    have hk :
        (∫ y : ℝ, k (ξ * y)) = |ξ⁻¹| • ∫ y : ℝ, k y := by
      simpa using (MeasureTheory.Measure.integral_comp_mul_left (g := k) (a := ξ))
    have hk_eval :
        (fun y : ℝ => k (ξ * y)) =
          fun y : ℝ => g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) := by
      funext y
      -- simplify `(ξ*y)/ξ = y`
      have hdiv : (ξ * y) / ξ = y := by
        field_simp [hξ]
      -- simplify the HO Gaussian at `ξ*y`
      have hpow : (ξ * y) ^ 2 / (2 * ξ ^ 2) = y ^ 2 / 2 := by
        field_simp [hξ]
      have hneg : - (ξ * y) ^ 2 / (2 * ξ ^ 2) = -y ^ 2 / 2 := by
        have := congrArg (fun t : ℝ => -t) hpow
        simpa [neg_div] using this
      -- unfold `k` and rewrite the transformed factors
      dsimp [k]
      simpa [gaussianHO, hdiv, hneg]
    have hk_int :
        ∫ y : ℝ, g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) =
          |ξ⁻¹| • ∫ y : ℝ, g y * physHermite n (y / ξ) * gaussianHO ξ y := by
      -- combine the two previous facts
      have hk' :
          ∫ y : ℝ, g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) =
            |ξ⁻¹| • ∫ y : ℝ, k y := by
        simpa [hk_eval] using hk
      simpa [k] using hk'
    -- The RHS is exactly the assumed `horth n`.
    have horth_k : ∫ y : ℝ, g y * physHermite n (y / ξ) * gaussianHO ξ y = 0 := by
      -- unfold `eigenfunctionReal` and use `horth`
      have := horth n
      simpa [eigenfunctionReal, gaussianHO, mul_assoc, mul_left_comm, mul_comm] using this
    -- Therefore the Lebesgue integral in `hk_int` is `0`.
    have hk0 :
        ∫ y : ℝ, g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) = 0 := by
      -- the scalar multiple of zero is zero
      rw [hk_int, horth_k]
      simp
    -- Now identify the `gaussMeasure` integral with this Lebesgue integral.
    -- `h y * exp(-y^2) = g(ξ*y) * exp(-y^2/2)`.
    have hpoint :
        (fun y : ℝ =>
            (ENNReal.ofReal (Real.exp (-y ^ 2))).toReal *
              (h y * (Polynomial.aeval y) (physHermite n))) =
          fun y : ℝ =>
            g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) := by
      funext y
      -- cancel the Gaussian density against the exponential factor in `h`
      calc
        (ENNReal.ofReal (Real.exp (-y ^ 2))).toReal * (h y * (Polynomial.aeval y) (physHermite n))
            = Real.exp (-y ^ 2) * (g (ξ * y) * Real.exp (y ^ 2 / 2) * physHermite n y) := by
                simp [h, ENNReal.toReal_ofReal (Real.exp_nonneg _), mul_assoc, physHermite_eq_aeval]
        _ = g (ξ * y) * (Real.exp (-y ^ 2) * (Real.exp (y ^ 2 / 2) * physHermite n y)) := by
              ring_nf
        _ = g (ξ * y) * (Real.exp (-y ^ 2 / 2) * physHermite n y) := by
              simp [exp_neg_sq_mul_exp_sq_half_mul]
        _ = g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) := by
              ring_nf
    -- assemble
    have : (∫ y : ℝ, h y * physHermite n y ∂PhysHermiteGauss.gaussMeasure) =
          ∫ y : ℝ, g (ξ * y) * physHermite n y * Real.exp (-y ^ 2 / 2) := by
      -- unfold `gaussMeasure` and use `hwd`
      simpa [PhysHermiteGauss.gaussMeasure_def, ρ, hpoint] using hwd
    rw [this]
    exact hk0
  -- Apply the Gaussian-weight completeness theorem.
  have hzero_gauss : h =ᵐ[PhysHermiteGauss.gaussMeasure] 0 :=
    PhysHermiteGauss.ae_eq_zero_of_forall_integral_physHermite_eq_zero (g := h) hh_memLp horth'
  -- Since the density is everywhere nonzero, this gives `h = 0` a.e. for Lebesgue.
  have hzero_vol : h =ᵐ[(volume : Measure ℝ)] 0 := by
    -- use `ae_withDensity_iff` on the predicate `h y = 0`
    have hρ_nonzero : ∀ y : ℝ, (ENNReal.ofReal (Real.exp (-y ^ 2)) : ℝ≥0∞) ≠ 0 := by
      intro y
      simp [Real.exp_pos]
    let f : ℝ → ℝ≥0∞ := fun y => (ENNReal.ofReal (Real.exp (-y ^ 2)) : ℝ≥0∞)
    have hf_meas : Measurable f := by fun_prop
    have hwd_ae : (∀ᵐ y : ℝ ∂(volume : Measure ℝ).withDensity f, h y = 0) := by
      simpa [PhysHermiteGauss.gaussMeasure_def, f] using hzero_gauss
    have haewd :
        (∀ᵐ y : ℝ ∂(volume : Measure ℝ).withDensity f, h y = 0) ↔
          ∀ᵐ y : ℝ ∂(volume : Measure ℝ), f y ≠ 0 → h y = 0 :=
      MeasureTheory.ae_withDensity_iff (μ := (volume : Measure ℝ)) (f := f) (p := fun y => h y = 0)
        hf_meas
    have hvol' : (∀ᵐ y : ℝ ∂(volume : Measure ℝ), f y ≠ 0 → h y = 0) :=
      (haewd.1 hwd_ae)
    -- density is never zero
    filter_upwards [hvol'] with y hy
    exact hy (by simpa [f] using hρ_nonzero y)
  -- From `h = 0` a.e. and `exp(y^2/2) ≠ 0`, deduce `g (ξ*y) = 0` a.e.
  have hcomp : (fun y : ℝ => g (ξ * y)) =ᵐ[(volume : Measure ℝ)] 0 := by
    filter_upwards [hzero_vol] with y hy
    have hexp : Real.exp (y ^ 2 / 2) ≠ 0 := exp_sq_half_ne_zero y
    -- `h y = g(ξ*y) * exp(...)`
    have : g (ξ * y) * Real.exp (y ^ 2 / 2) = 0 := by simpa [h] using hy
    exact (mul_eq_zero.mp this).resolve_right hexp
  -- Finally, invert the scaling to conclude `g = 0` a.e.
  exact ae_eq_zero_of_ae_comp_mul_left (ξ := ξ) hξ (g := g) hcomp

end HarmonicOscillator

end

end PhysLean

