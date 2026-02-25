/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import OSforGFF.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces (Bessel potential spaces)

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap LineDeriv Real

section TemperedFourierMultiplierCompat

variable [NormedSpace ℂ F]

/-- Fourier multiplier on tempered distributions (compat API). -/
def fourierMultiplierCLM (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (g : E → ℂ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  FourierTransform.fourierInvCLM ℂ 𝓢'(E, F) ∘L
    TemperedDistribution.smulLeftCLM F g ∘L
    FourierTransform.fourierCLM ℂ 𝓢'(E, F)

theorem fourierMultiplierCLM_apply (g : E → ℂ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g f = 𝓕⁻ (TemperedDistribution.smulLeftCLM F g (𝓕 f)) := by
  rfl

@[simp]
theorem fourier_fourierMultiplierCLM (g : E → ℂ) (f : 𝓢'(E, F)) :
    𝓕 (fourierMultiplierCLM F g f) = TemperedDistribution.smulLeftCLM F g (𝓕 f) := by
  simp [fourierMultiplierCLM]

private theorem fourier_injective : Function.Injective (fun h : 𝓢'(E, F) => 𝓕 h) := by
  intro a b hab
  have h := congrArg (fun t : 𝓢'(E, F) => 𝓕⁻ t) hab
  simpa using h

theorem fourierMultiplierCLM_fourierMultiplierCLM_apply {g₁ g₂ : E → ℂ}
    (hg₁ : g₁.HasTemperateGrowth) (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F g₁ (fourierMultiplierCLM F g₂ f) =
      fourierMultiplierCLM F (g₁ * g₂) f := by
  apply fourier_injective (E := E) (F := F)
  simp [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply, hg₁, hg₂]
  ext x
  simp [mul_comm]

theorem fourierMultiplierCLM_smul_apply {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (c : ℂ) (f : 𝓢'(E, F)) :
    fourierMultiplierCLM F (c • g) f = c • fourierMultiplierCLM F g f := by
  apply fourier_injective (E := E) (F := F)
  simp [TemperedDistribution.smulLeftCLM_smul (F := F) hg c]

theorem fourierMultiplierCLM_const (c : ℂ) :
    fourierMultiplierCLM F (fun _ : E ↦ c) = c • ContinuousLinearMap.id ℂ _ := by
  ext1 f
  apply fourier_injective (E := E) (F := F)
  simp [fourierMultiplierCLM]

theorem fourierMultiplierCLM_sum {ι : Type*} {g : ι → E → ℂ} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    fourierMultiplierCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, fourierMultiplierCLM F (g i) := by
  ext1 f
  apply fourier_injective (E := E) (F := F)
  simp [TemperedDistribution.smulLeftCLM_sum hg]

theorem lineDeriv_eq_fourierMultiplierCLM (m : E) (f : 𝓢'(E, F)) :
    ∂_{m} f = (2 * Real.pi * Complex.I) • fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x m : ℂ)) f := by
  apply fourier_injective (E := E) (F := F)
  simp [TemperedDistribution.fourier_lineDerivOp_eq]

open scoped Laplacian

theorem laplacian_eq_fourierMultiplierCLM (f : 𝓢'(E, F)) :
    Δ f = (-(2 * Real.pi) ^ 2 : ℂ) •
      fourierMultiplierCLM F (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) f := by
  let ι := Fin (Module.finrank ℝ E)
  let b : OrthonormalBasis ι ℝ E := stdOrthonormalBasis ℝ E
  let c : ℂ := 2 * Real.pi * Complex.I
  have hinner : ∀ i : ι, (fun x : E ↦ (inner ℝ x (b i) : ℂ)).HasTemperateGrowth := by
    intro i
    fun_prop
  have hcomp (i : ι) :
      fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ))
        (fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ)) f) =
      fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
    simpa using fourierMultiplierCLM_fourierMultiplierCLM_apply
      (E := E) (F := F)
      (g₁ := fun x : E ↦ (inner ℝ x (b i) : ℂ))
      (g₂ := fun x : E ↦ (inner ℝ x (b i) : ℂ))
      (hg₁ := hinner i) (hg₂ := hinner i) (f := f)
  have hsumMul :
      (∑ i : ι, fourierMultiplierCLM F
          (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f)
        =
      fourierMultiplierCLM F
        (fun x : E ↦ ∑ i : ι, (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
    simpa using
      congrArg (fun T : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) ↦ T f)
        (fourierMultiplierCLM_sum (E := E) (F := F)
          (g := fun i : ι ↦ fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ))
          (s := Finset.univ)
          (by
            intro i hi
            have h1 : (fun x : E ↦ (inner ℝ x (b i) : ℂ)).HasTemperateGrowth := hinner i
            simpa [pow_two] using h1.mul h1)).symm
  have hc2 : c * c = (-(2 * Real.pi) ^ 2 : ℂ) := by
    dsimp [c]
    ring_nf
    simp [Complex.I_sq]
  calc
    Δ f = ∑ i : ι, ∂_{b i} (∂_{b i} f) := by
      simpa [b] using TemperedDistribution.laplacian_eq_sum (b := b) (f := f)
    _ = ∑ i : ι, c •
        (c • fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ))
          (fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ)) f)) := by
          simp [lineDeriv_eq_fourierMultiplierCLM (E := E) (F := F), c, map_smul]
    _ = ∑ i : ι, (c * c) •
        fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            c •
              (c • fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ))
                (fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ)) f))
                = (c * c) •
                fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ))
                  (fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ)) f) := by
                    simp [smul_smul]
            _ = (c * c) •
                fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
                    rw [hcomp i]
    _ = (c * c) • ∑ i : ι,
          fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
          simpa using
            (Finset.smul_sum
              (s := (Finset.univ : Finset ι))
              (r := c * c)
              (f := fun i : ι ↦
                fourierMultiplierCLM F (fun x : E ↦ (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f)).symm
    _ = (c * c) • fourierMultiplierCLM F
          (fun x : E ↦ ∑ i : ι, (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
          rw [hsumMul]
    _ = (-(2 * Real.pi) ^ 2 : ℂ) • fourierMultiplierCLM F
          (fun x : E ↦ ∑ i : ι, (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ)) f := by
          simp [hc2]
    _ = (-(2 * Real.pi) ^ 2 : ℂ) •
          fourierMultiplierCLM F (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) f := by
          have hnorm :
              (fun x : E ↦ ∑ i : ι, (inner ℝ x (b i) : ℂ) * (inner ℝ x (b i) : ℂ))
                = (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)) := by
            funext x
            norm_cast
            simpa [pow_two] using b.sum_sq_inner_left x
          simp [hnorm]

private theorem smulLeftCLM_toTemperedDistributionCLM_eq (g : E → ℂ) (f : 𝓢(E, F)) :
    TemperedDistribution.smulLeftCLM F g (f : 𝓢'(E, F)) =
      (SchwartzMap.smulLeftCLM (F := F) g f : 𝓢'(E, F)) := by
  by_cases hg : g.HasTemperateGrowth
  · ext u
    simp [TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.smulLeftCLM_apply_apply, hg]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simp [smul_smul, mul_comm]
  · ext u
    simp [TemperedDistribution.smulLeftCLM, SchwartzMap.smulLeftCLM, hg]

theorem fourierMultiplierCLM_toTemperedDistributionCLM_eq {g : E → ℂ}
    (_hg : g.HasTemperateGrowth) [CompleteSpace F] (f : 𝓢(E, F)) :
    fourierMultiplierCLM F g (f : 𝓢'(E, F)) = (SchwartzMap.fourierMultiplierCLM F g f : 𝓢'(E, F)) := by
  calc
    fourierMultiplierCLM F g (f : 𝓢'(E, F))
        = 𝓕⁻ (TemperedDistribution.smulLeftCLM F g (𝓕 (f : 𝓢'(E, F)))) := by
            rfl
    _ = 𝓕⁻ (TemperedDistribution.smulLeftCLM F g ((𝓕 f : 𝓢(E, F)) : 𝓢'(E, F))) := by
          rw [TemperedDistribution.fourier_toTemperedDistributionCLM_eq (f := f)]
    _ = 𝓕⁻ (((SchwartzMap.smulLeftCLM (F := F) g (𝓕 f)) : 𝓢(E, F)) : 𝓢'(E, F)) := by
          congr 1
          exact smulLeftCLM_toTemperedDistributionCLM_eq (E := E) (F := F) (g := g) (f := 𝓕 f)
    _ = ((𝓕⁻ (SchwartzMap.smulLeftCLM (F := F) g (𝓕 f)) : 𝓢(E, F)) : 𝓢'(E, F)) := by
          rw [TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq
            (f := SchwartzMap.smulLeftCLM (F := F) g (𝓕 f))]
    _ = (SchwartzMap.fourierMultiplierCLM F g f : 𝓢'(E, F)) := by
          rfl

end TemperedFourierMultiplierCompat

section BesselPotential

section normed

variable [NormedSpace ℂ F]

variable (E F) in
def besselPotential (s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))

variable (E F) in
@[simp]
theorem besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id ℂ _ := by
  simpa [besselPotential] using (fourierMultiplierCLM_const (E := E) (F := F) (c := 1))

@[simp]
theorem besselPotential_besselPotential_apply (s s' : ℝ) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f := by
  simp_rw [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s' / 2 + s / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

theorem besselPotential_compL_besselPotential (s s' : ℝ) :
    besselPotential E F s' ∘L besselPotential E F s = besselPotential E F (s + s') := by
  ext1 f
  exact besselPotential_besselPotential_apply s s' f

open scoped Real Laplacian

theorem besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) :
    ((besselPotential E F (-2)) (Δ f)) = fourierMultiplierCLM F (fun x ↦ Complex.ofReal <|
      -(2 * π) ^ 2 * ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) f := calc
  _ = -(2 * π) ^ 2 • (fourierMultiplierCLM F
      (fun x ↦ Complex.ofReal <| (‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (- (1 : ℝ)))) f := by
    have hnormSq : (fun x : E ↦ Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth := by
      exact Function.HasTemperateGrowth.comp
        (Function.RCLike.hasTemperateGrowth_ofReal ℂ)
        (Function.hasTemperateGrowth_norm_sq (H := E))
    rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
      ContinuousLinearMap.map_smul]
    rw [fourierMultiplierCLM_fourierMultiplierCLM_apply
      (E := E) (F := F)
      (g₁ := fun x ↦ ((1 + ‖x‖ ^ 2) ^ (-2 / 2) : ℝ))
      (g₂ := fun x ↦ Complex.ofReal (‖x‖ ^ 2))
      (hg₁ := by fun_prop) (hg₂ := hnormSq)]
    congr 2
    · norm_num
    · congr 1
      funext x
      simp [mul_comm]
  _ = _ := by
    rw [← Complex.coe_smul, ← fourierMultiplierCLM_smul_apply (by fun_prop)]
    congr 1
    congr 1
    funext x
    simp [smul_eq_mul, mul_comm, mul_left_comm]

end normed

section inner

variable [InnerProductSpace ℂ F]

open FourierTransform

@[simp]
theorem fourier_besselPotential_eq_smulLeftCLM_fourierInv_apply (s : ℝ) (f : 𝓢'(E, F)) :
    𝓕 (besselPotential E F s f) =
      smulLeftCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) := by
  simp [besselPotential, fourierMultiplierCLM]

end inner

end BesselPotential

section normed

variable [NormedSpace ℂ F] [CompleteSpace F]

def MemSobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  ∃ (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

theorem memSobolev_zero_iff {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    ∃ (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]

theorem memSobolev_add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  change _ = Lp.toTemperedDistributionCLM F volume p (f' + g')
  simp [map_add, hf, hg]

theorem memSobolev_smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  change _ = Lp.toTemperedDistributionCLM F volume p (c • f')
  simp [hf]

variable (E F) in
theorem memSobolev_zero (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  change _ = Lp.toTemperedDistributionCLM F volume p 0
  simp only [map_zero]

@[simp]
theorem memSobolev_besselPotential_iff {s r : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} :
    MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r + s) p f := by
  simp [MemSobolev]

/-- Schwartz functions are in every Sobolev space. -/
theorem memSobolev_toTemperedDistributionCLM {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    MemSobolev s p (f : 𝓢'(E, F)) := by
  use (SchwartzMap.fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f).toLp p
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

variable (E F) in
structure Sobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] where
  toDistr : 𝓢'(E, F)
  sobFn : Lp F p (volume : Measure E)
  bessel_toDistr_eq_sobFn : besselPotential E F s toDistr = sobFn

namespace Sobolev

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

theorem ext' {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : Sobolev E F s p}
    (h₁ : f.toDistr = g.toDistr) (h₂ : f.sobFn = g.sobFn) : f = g := by
  cases f; cases g; congr

theorem memSobolev_toDistr (f : Sobolev E F s p) : MemSobolev s p f.toDistr :=
  ⟨f.sobFn, f.bessel_toDistr_eq_sobFn⟩

@[simp]
theorem besselPotential_neg_sobFn_eq {f : Sobolev E F s p} :
    besselPotential E F (-s) f.sobFn = f.toDistr := by
  simp [← f.bessel_toDistr_eq_sobFn]

@[ext]
theorem ext {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : Sobolev E F s p}
    (h₁ : f.toDistr = g.toDistr) : f = g := by
  apply ext' h₁
  apply_fun MeasureTheory.Lp.toTemperedDistribution; swap
  · apply LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  calc
    f.sobFn = besselPotential E F s f.toDistr := f.bessel_toDistr_eq_sobFn.symm
    _ = besselPotential E F s g.toDistr := by congr
    _ = g.sobFn := g.bessel_toDistr_eq_sobFn

def _root_.MemSobolev.toSobolev {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : Sobolev E F s p where
  toDistr := f
  sobFn := hf.choose
  bessel_toDistr_eq_sobFn := hf.choose_spec

def copy {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {s s' : ℝ} (hs : s = s') (f : Sobolev E F s p) :
    Sobolev E F s' p where
  toDistr := f.toDistr
  sobFn := f.sobFn
  bessel_toDistr_eq_sobFn := by
    rw [← hs]
    exact f.bessel_toDistr_eq_sobFn

@[simp]
theorem _root_.MemSobolev.toSobolev_toDistr {f : 𝓢'(E, F)} (hf : MemSobolev s p f) :
    hf.toSobolev.toDistr = f := rfl

theorem _root_.MemSobolev.toSobolev_injective {f g : 𝓢'(E, F)} (hf : MemSobolev s p f)
    (hg : MemSobolev s p g) (h : hf.toSobolev = hg.toSobolev) : f = g := by
  rw [← hf.toSobolev_toDistr, ← hg.toSobolev_toDistr, h]

variable (E F s p) in
theorem injective_sobFn :
    Function.Injective (sobFn (s := s) (p := p) (E := E) (F := F)) := by
  intro f g hfg
  refine ext' ?_ hfg
  calc
    f.toDistr = besselPotential E F (-s) (Sobolev.sobFn f) := by simp
    _ = besselPotential E F (-s) (Sobolev.sobFn g) := by congr
    _ = g.toDistr := by simp

instance instZero : Zero (Sobolev E F s p) where
  zero := {
    toDistr := 0
    sobFn := 0
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [-Lp.toTemperedDistributionCLM_apply] }

instance instAdd : Add (Sobolev E F s p) where
  add f g := {
    toDistr := f.toDistr + g.toDistr
    sobFn := f.sobFn + g.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ + _)
      simp [map_add, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_add (f g : Sobolev E F s p) : (f + g).toDistr = f.toDistr + g.toDistr := rfl

instance instSub : Sub (Sobolev E F s p) where
  sub f g := {
    toDistr := f.toDistr - g.toDistr
    sobFn := f.sobFn - g.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ - _)
      simp [map_sub, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

instance instNeg : Neg (Sobolev E F s p) where
  neg f := {
    toDistr := -f.toDistr
    sobFn := -f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (- _)
      simp [map_neg, f.bessel_toDistr_eq_sobFn] }

instance instNSMul : SMul ℕ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [f.bessel_toDistr_eq_sobFn] }

instance instZSMul : SMul ℤ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [f.bessel_toDistr_eq_sobFn] }

/- Generalize this-/
instance instSMul : SMul ℂ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [map_smul, f.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_smul (c : ℂ) (f : Sobolev E F s p) : (c • f).toDistr = c • f.toDistr := rfl

instance instAddCommGroup : AddCommGroup (Sobolev E F s p) :=
  (injective_sobFn E F s p).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F s p) in
/-- Coercion as an additive homomorphism. -/
def coeHom : Sobolev E F s p →+ 𝓢'(E, F) where
  toFun f := f.toDistr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeHom_injective : Function.Injective (coeHom E F s p) := by
  apply ext

instance instModule : Module ℂ (Sobolev E F s p) :=
  coeHom_injective.module ℂ (coeHom E F s p) fun _ _ => rfl

variable (E F s p) in
def toLpₗ : Sobolev E F s p →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := sobFn
  map_add' f g := by rfl
  map_smul' c f := by rfl

@[simp]
theorem toLpₗ_apply (f : Sobolev E F s p) :
    toLpₗ E F s p f = sobFn f := rfl

theorem sobFn_add (f g : Sobolev E F s p) :
    sobFn (f + g) = sobFn f + sobFn g := rfl

theorem sobFn_smul (c : ℂ) (f : Sobolev E F s p) :
    sobFn (c • f) = c • sobFn f := rfl

instance instNormedAddCommGroup :
    NormedAddCommGroup (Sobolev E F s p) :=
  NormedAddCommGroup.induced (Sobolev E F s p) (Lp F p (volume : Measure E)) (toLpₗ E F s p)
    (injective_sobFn E F s p)

@[simp]
theorem norm_sobFn_eq (f : Sobolev E F s p) : ‖f.sobFn‖ = ‖f‖ :=
  rfl

instance instNormedSpace :
    NormedSpace ℂ (Sobolev E F s p) where
  norm_smul_le c f := by
    simp_rw [← norm_sobFn_eq, ← norm_smul]
    rfl

variable (E F s p) in
def toLpₗᵢ :
    Sobolev E F s p →ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  norm_map' _ := rfl

end Sobolev

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memSobolev_two_iff_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  rw [MemSobolev]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourierInv_apply] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential, fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']

theorem memSobolev_zero_two_iff_fourierTransform {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_two_iff_fourier]

/-- The Fourier transform of a Sobolev function of order `s` with `s > d / 2` can be represented by
a `L1` function.

This is the main calculation of the Sobolev embedding theorem. -/
theorem MemSobolev.fourier_memL1 {s : ℝ} (hs : Module.finrank ℝ E < 2 * s) {f : 𝓢'(E, F)}
    (hf : MemSobolev s 2 f) :
    ∃ (v : Lp F 1 (volume : Measure E)), 𝓕 f  = (v : 𝓢'(E, F)) := by
  obtain ⟨u, hu⟩ :=  memSobolev_two_iff_fourier.mp hf
  have : MemLp (fun (x : E) ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)) 2 := by
    constructor
    · have : (fun (x : E) ↦ (1 + ‖x‖ ^ 2) ^ (-s / 2)).HasTemperateGrowth := by
        fun_prop
      exact this.1.continuous.aestronglyMeasurable
    · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
      suffices h : ∫⁻ (a : E), ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-s)‖ < ⊤ from by
        norm_cast
        simp_rw [ofReal_norm] at h
        simp_rw [← enorm_pow]
        convert h using 4
        rw [← Real.rpow_mul_natCast (by positivity)]
        simp
      apply ((integrable_rpow_neg_one_add_norm_sq hs).congr _).lintegral_lt_top
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
      congr
      ring
  have : MemLp (fun (x : E) ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ)) 2 := this.ofReal
  use this.toLp • u
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
  · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    convert (smulLeftCLM_const 1 (𝓕 f)).symm using 1
    · simp
    · congr
      ext x
      rw [Pi.mul_apply]
      norm_cast
      rw [← Real.rpow_add (by positivity)]
      ring_nf
      simp
  · fun_prop

-- Todo:
-- FT of L1 is ZeroAtInfty (by extension from Schwartz)
-- Locally integrable & polynomially bounded functions define tempered distributions
-- ZeroAtInfty satisfies above conditions
-- The various FTs commute

open scoped BoundedContinuousFunction

theorem memSobolev_fourierMultiplierCLM_bounded {s : ℝ} {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∃ C, ∀ x, ‖g x‖ ≤ C) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s 2 (fourierMultiplierCLM F g f) := by
  rw [memSobolev_two_iff_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (g'.memLp_top.toLp _ (μ := volume)) • f'
  rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq (by apply hg₁), ← hf,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

theorem MemSobolev.mono {s s' : ℝ} (h : s' ≤ s) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s' 2 f := by
  have h' : (s' - s) / 2 ≤ 0 := by
    rw [div_le_iff₀ (by norm_num)]
    simp [h]
  have hs : s' = (s' - s) + s := by ring
  rw [hs, ← memSobolev_besselPotential_iff]
  apply memSobolev_fourierMultiplierCLM_bounded (by fun_prop) _ hf
  use 1
  intro x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) h'

section LineDeriv

open scoped LineDeriv Laplacian Real

/-- The Laplacian maps `H^{s}` to `H^{s - 2}`.

The other implication is slightly harder :-) -/
theorem MemSobolev.laplacian {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev (s - 2) 2 (Δ f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 2, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_two_laplacian_eq f]
  apply memSobolev_fourierMultiplierCLM_bounded (by fun_prop) _ hf
  use (2 * π) ^ 2
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [pow_one, norm_mul, norm_pow, norm_inv, Real.norm_eq_abs]
  simp only [abs_neg, abs_pow, abs_mul, Nat.abs_ofNat, abs_norm]
  have : 0 < π := by positivity
  rw [abs_of_pos this]
  rw [mul_inv_le_iff₀]
  · gcongr
    grind
  norm_cast
  positivity

end LineDeriv

namespace Sobolev

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (Sobolev E F s 2) where
  inner f g := inner ℂ f.sobFn g.sobFn
  norm_sq_eq_re_inner f := by simp; norm_cast
  conj_inner_symm f g := by simp
  add_left f g h := by rw [sobFn_add, inner_add_left]
  smul_left f g c := by rw [sobFn_smul, inner_smul_left]

open Laplacian

instance instLaplacian (s : ℝ) : Laplacian (Sobolev E F s 2) (Sobolev E F (s - 2) 2) where
  laplacian f := f.memSobolev_toDistr.laplacian.toSobolev

@[simp]
theorem laplacian_toDistr {s : ℝ} (f : Sobolev E F s 2) : (Δ f).toDistr = Δ f.toDistr := rfl

def laplacianₗ {s : ℝ} : Sobolev E F s 2 →ₗ[ℂ] Sobolev E F (s - 2) 2 where
  toFun := Δ
  map_add' f g := by
    ext1
    simpa using (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_add f.toDistr g.toDistr
  map_smul' c f := by
    ext1
    simpa only [laplacian_toDistr, laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_smul c f.toDistr

end Sobolev

end inner
