/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeL2Basis

/-!
# `L²`-completeness of product Hermite eigenfunctions on `Fin n → ℝ`

This file lifts the 1D completeness of the harmonic-oscillator eigenfunctions
`HarmonicOscillator.eigenfunctionReal ξ n` to finite products `Fin n → ℝ` using Fubini and induction.
-/

open scoped BigOperators ENNReal RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

open scoped InnerProductSpace

/-- If `g ∈ L²(ℝ × (Fin n → ℝ))`, then almost every `z`-slice is in `L²(Fin n → ℝ)`. -/
lemma ae_memLp_two_slice_of_memLp_two_prod
    {n : ℕ} {g : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg : MemLp g 2 (volume : Measure (ℝ × (Fin n → ℝ)))) :
    ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      MemLp (fun z : (Fin n → ℝ) => g (x0, z)) 2 (volume : Measure (Fin n → ℝ)) := by
  have hslice_meas :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        AEStronglyMeasurable (fun z : (Fin n → ℝ) => g (x0, z))
          (volume : Measure (Fin n → ℝ)) := by
    simpa using
      (hg.1.prodMk_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
  have hslice_sq_int :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        Integrable (fun z : (Fin n → ℝ) => (g (x0, z)) ^ 2)
          (volume : Measure (Fin n → ℝ)) := by
    simpa using (MeasureTheory.MemLp.integrable_sq hg).prod_right_ae
  filter_upwards [hslice_meas, hslice_sq_int] with x0 hmeas hint
  exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hint

/-- If the squared slices integrate to `0` almost everywhere, then the squared product integral is `0`. -/
lemma integral_sq_eq_zero_of_ae_integral_sq_eq_zero
    {n : ℕ} {g : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg_int : Integrable (fun p : (ℝ × (Fin n → ℝ)) => (g p) ^ 2)
      (volume : Measure (ℝ × (Fin n → ℝ))))
    (hinner_ae : ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      (∫ z : (Fin n → ℝ), (g (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) = 0) :
    (∫ p : (ℝ × (Fin n → ℝ)), (g p) ^ 2 ∂(volume : Measure (ℝ × (Fin n → ℝ)))) = 0 := by
  have hfub :
      (∫ p : (ℝ × (Fin n → ℝ)), (g p) ^ 2 ∂(volume : Measure (ℝ × (Fin n → ℝ))))
        =
      ∫ x0 : ℝ,
        ∫ z : (Fin n → ℝ), (g (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))
          ∂(volume : Measure ℝ) := by
    simpa using
      (MeasureTheory.integral_prod
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
        (f := fun p : (ℝ × (Fin n → ℝ)) => (g p) ^ 2) hg_int)
  rw [hfub]
  exact MeasureTheory.integral_eq_zero_of_ae (μ := (volume : Measure ℝ)) hinner_ae

/-- A real-valued `L²` function is almost everywhere zero if the integral of its square vanishes. -/
lemma ae_eq_zero_of_integrable_sq_integral_sq_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg_int : Integrable (fun x => (g x) ^ 2) μ)
    (hzero : (∫ x, (g x) ^ 2 ∂μ) = 0) :
    g =ᵐ[μ] 0 := by
  have hnonneg : 0 ≤ᵐ[μ] fun x => (g x) ^ 2 :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hsq_ae : (fun x => (g x) ^ 2) =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hg_int).1 hzero
  filter_upwards [hsq_ae] with x hx
  exact eq_zero_of_pow_eq_zero (n := 2) (by simpa using hx)

private lemma ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero_zero
    (ξ : ℝ) {g : (Fin 0 → ℝ) → ℝ}
    (horth : ∀ k : Fin 0 → ℕ,
      ∫ x : (Fin 0 → ℝ), g x * eigenfunctionProd (n := 0) ξ k x = 0) :
    g =ᵐ[(volume : Measure (Fin 0 → ℝ))] 0 := by
  let x0 : (Fin 0 → ℝ) := fun _ : Fin 0 => (0 : ℝ)
  have hμ : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac x0 := by
    simpa using
      (MeasureTheory.Measure.volume_pi_eq_dirac
        (ι := Fin 0) (α := fun _ : Fin 0 => ℝ) (x := x0))
  have h0 : (∫ x : (Fin 0 → ℝ), g x ∂(volume : Measure (Fin 0 → ℝ))) = 0 := by
    have := horth (fun i : Fin 0 => (nomatch i))
    simpa [eigenfunctionProd, mul_one] using this
  have hgx0 : g x0 = 0 := by
    have : (∫ x : (Fin 0 → ℝ), g x ∂(Measure.dirac x0)) = 0 := by simpa [hμ] using h0
    simpa using this
  have hg0 : g = 0 := by
    funext x
    have : x = x0 := Subsingleton.elim x x0
    simp [this, hgx0]
  simp [hg0]

private lemma ae_eq_zero_of_comp_piFinSuccAbove
    {n : ℕ}
    (e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)))
    (hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
      (volume : Measure (ℝ × (Fin n → ℝ))))
    {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg' : (fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y))
      =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] 0) :
    g =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] 0 := by
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving e
      (volume : Measure (Fin (n + 1) → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) :=
    hmp.quasiMeasurePreserving
  have hcomp :
      (fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y)) ∘ e
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))]
          (0 : (ℝ × (Fin n → ℝ)) → ℝ) ∘ e :=
    hq.ae_eq_comp hg'
  have hcomp0 :
      (fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y)) ∘ e
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] 0 := by
    simpa using hcomp
  have hge :
      (fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y)) ∘ e
        =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] g := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simp
  exact hge.symm.trans hcomp0

private lemma ae_all_eq_zero_of_forall_ae_eq_zero
    {α ι : Type*} [MeasurableSpace α] [Countable ι] {μ : Measure α} {f : α → ι → ℝ}
    (h : ∀ i : ι, (fun x : α => f x i) =ᵐ[μ] 0) :
    ∀ᵐ x : α ∂μ, ∀ i : ι, f x i = 0 := by
  refine (MeasureTheory.ae_all_iff).2 ?_
  intro i
  simpa using h i

private lemma integral_sq_eq_zero_of_ae_eq_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg0 : g =ᵐ[μ] 0) :
    (∫ x : α, (g x) ^ 2 ∂μ) = 0 := by
  have hsq0 : (fun x : α => (g x) ^ 2) =ᵐ[μ] 0 := by
    filter_upwards [hg0] with x hx
    simp [hx]
  exact MeasureTheory.integral_eq_zero_of_ae (μ := μ) hsq0

private lemma ae_eq_zero_of_ae_slice_eq_zero
    {n : ℕ} {g : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg : MemLp g 2 (volume : Measure (ℝ × (Fin n → ℝ))))
    (hslice_zero : ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      (fun z : (Fin n → ℝ) => g (x0, z)) =ᵐ[(volume : Measure (Fin n → ℝ))] 0) :
    g =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] 0 := by
  have hsq_int : Integrable (fun p : (ℝ × (Fin n → ℝ)) => (g p) ^ 2)
      (volume : Measure (ℝ × (Fin n → ℝ))) := MeasureTheory.MemLp.integrable_sq hg
  have hinner_ae : ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      (∫ z : (Fin n → ℝ), (g (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) = 0 := by
    filter_upwards [hslice_zero] with x0 hx0
    exact integral_sq_eq_zero_of_ae_eq_zero (μ := (volume : Measure (Fin n → ℝ)))
      (g := fun z : (Fin n → ℝ) => g (x0, z)) hx0
  have hsq_zero := integral_sq_eq_zero_of_ae_integral_sq_eq_zero (n := n) (g := g) hsq_int hinner_ae
  exact ae_eq_zero_of_integrable_sq_integral_sq_eq_zero
    (μ := (volume : Measure (ℝ × (Fin n → ℝ)))) (g := g) hsq_int hsq_zero

private lemma ae_coeffFun_zero_of_forall_integral_eigenfunctionReal_eq_zero
    {ι : Type*} (ξ : ℝ) (hξ : ξ ≠ 0) {F : ι → ℝ → ℝ}
    (hF_memLp : ∀ i : ι, MemLp (F i) 2 (volume : Measure ℝ))
    (hF_orth : ∀ i : ι, ∀ k0 : ℕ, ∫ x0 : ℝ, (F i x0) * eigenfunctionReal ξ k0 x0 = 0) :
    ∀ i : ι, (F i) =ᵐ[(volume : Measure ℝ)] 0 := by
  intro i
  refine HarmonicOscillator.ae_eq_zero_of_forall_integral_eigenfunctionReal_eq_zero
    (ξ := ξ) hξ (hg := hF_memLp i) ?_
  intro k0
  simpa [mul_assoc] using hF_orth i k0

private lemma ae_slice_zero_of_ae_memLp_and_ae_orthogonality
    {n : ℕ} {ξ : ℝ}
    (ih : ∀ {g : (Fin n → ℝ) → ℝ}, MemLp g 2 (volume : Measure (Fin n → ℝ)) →
      (∀ k : Fin n → ℕ, ∫ z : (Fin n → ℝ), g z * eigenfunctionProd (n := n) ξ k z = 0) →
      g =ᵐ[(volume : Measure (Fin n → ℝ))] 0)
    {g : (ℝ × (Fin n → ℝ)) → ℝ}
    (hslice_memLp : ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      MemLp (fun z : (Fin n → ℝ) => g (x0, z)) 2 (volume : Measure (Fin n → ℝ)))
    (horth_ae : ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      ∀ k : Fin n → ℕ, ∫ z : (Fin n → ℝ), g (x0, z) * eigenfunctionProd (n := n) ξ k z = 0) :
    ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
      (fun z : (Fin n → ℝ) => g (x0, z)) =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
  filter_upwards [hslice_memLp, horth_ae] with x0 hx0 horth0
  exact ih (g := fun z : (Fin n → ℝ) => g (x0, z)) hx0 horth0

private lemma integral_eq_zero_on_prod_of_integral_eq_zero_on_piFinSuccAbove
    {n : ℕ} {ξ : ℝ}
    (e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)))
    (hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
      (volume : Measure (ℝ × (Fin n → ℝ))))
    {g : (Fin (n + 1) → ℝ) → ℝ} {g' : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg' : g' = fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y))
    (k : Fin (n + 1) → ℕ)
    (hk : (∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x) = 0) :
    (∫ y : (ℝ × (Fin n → ℝ)), g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)) = 0 := by
  let φ : (ℝ × (Fin n → ℝ)) → ℝ :=
    fun y => g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)
  change (∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ)))) = 0
  have hcomp :
      (∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ))) =
        ∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ))) :=
    (MeasurePreserving.integral_comp'
      (μ := (volume : Measure (Fin (n + 1) → ℝ)))
      (ν := (volume : Measure (ℝ × (Fin n → ℝ)))) hmp (g := φ))
  have hφ :
      (∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ))) =
        ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x
          ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
    refine MeasureTheory.integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [φ, hg']
  calc
    (∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ))))
        =
      ∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
          simpa using hcomp.symm
    _ =
      ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x
          ∂(volume : Measure (Fin (n + 1) → ℝ)) := hφ
    _ = 0 := by simpa using hk

private lemma memLp_coeffFun_of_memLp_prod
    {n : ℕ} {ξ : ℝ} (hξ : ξ ≠ 0)
    {g' : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg' : MemLp g' 2 (volume : Measure (ℝ × (Fin n → ℝ))))
    (krest : Fin n → ℕ) :
    MemLp
      (fun x0 : ℝ =>
        ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
          ∂(volume : Measure (Fin n → ℝ)))
      2 (volume : Measure ℝ) := by
  let F : ℝ → ℝ :=
    fun x0 =>
      ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
        ∂(volume : Measure (Fin n → ℝ))
  have hH_meas_prod :
      AEStronglyMeasurable
        (fun p : ℝ × (Fin n → ℝ) => eigenfunctionProd (n := n) ξ krest p.2)
        (volume : Measure (ℝ × (Fin n → ℝ))) := by
    have hH_meas :
        AEStronglyMeasurable (eigenfunctionProd (n := n) ξ krest)
          (volume : Measure (Fin n → ℝ)) :=
      aestronglyMeasurable_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) krest
    exact hH_meas.comp_quasiMeasurePreserving
      (by
        simpa using
          (MeasureTheory.Measure.quasiMeasurePreserving_snd
            (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))))
  have h_integrand_meas :
      AEStronglyMeasurable
        (fun p : ℝ × (Fin n → ℝ) => g' p * eigenfunctionProd (n := n) ξ krest p.2)
        (volume : Measure (ℝ × (Fin n → ℝ))) :=
    hg'.1.mul hH_meas_prod
  have hF_meas : AEStronglyMeasurable F (volume : Measure ℝ) := by
    simpa [F] using
      (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))) h_integrand_meas)
  have hgsq_int :
      Integrable (fun p : ℝ × (Fin n → ℝ) => (g' p) ^ 2)
        (volume : Measure (ℝ × (Fin n → ℝ))) :=
    MeasureTheory.MemLp.integrable_sq hg'
  have hslice_memLp :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        MemLp (fun z : (Fin n → ℝ) => g' (x0, z)) 2
          (volume : Measure (Fin n → ℝ)) :=
    ae_memLp_two_slice_of_memLp_two_prod (n := n) (g := g') hg'
  let C : ℝ :=
    ∫ z : (Fin n → ℝ), (eigenfunctionProd (n := n) ξ krest z) ^ 2
      ∂(volume : Measure (Fin n → ℝ))
  have hC_nonneg : 0 ≤ C := by
    refine integral_nonneg ?_
    intro z
    exact sq_nonneg _
  have hG2_int :
      Integrable
        (fun x0 : ℝ =>
          ∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ)))
        (volume : Measure ℝ) := by
    simpa using hgsq_int.integral_prod_left
  have hbound :
      (fun x0 : ℝ => (F x0) ^ 2) ≤ᵐ[(volume : Measure ℝ)]
        fun x0 : ℝ =>
          C * (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) := by
    filter_upwards [hslice_memLp] with x0 hx0
    let gz : (Fin n → ℝ) → ℝ := fun z => g' (x0, z)
    have hH : MemLp (eigenfunctionProd (n := n) ξ krest) 2 (volume : Measure (Fin n → ℝ)) :=
      memLp_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) krest
    have hinner :
        (∫ z : (Fin n → ℝ), gz z * eigenfunctionProd (n := n) ξ krest z
            ∂(volume : Measure (Fin n → ℝ)))
          *
        (∫ z : (Fin n → ℝ), gz z * eigenfunctionProd (n := n) ξ krest z
            ∂(volume : Measure (Fin n → ℝ)))
          ≤
        (∫ z : (Fin n → ℝ), (gz z) ^ 2 ∂(volume : Measure (Fin n → ℝ))) * C := by
      let u : (Fin n → ℝ) →₂[(volume : Measure (Fin n → ℝ))] ℝ := hx0.toLp gz
      let v : (Fin n → ℝ) →₂[(volume : Measure (Fin n → ℝ))] ℝ :=
        hH.toLp (eigenfunctionProd (n := n) ξ krest)
      have hu_ae : (fun z : (Fin n → ℝ) => u z) =ᵐ[(volume : Measure (Fin n → ℝ))] gz := by
        simpa [u] using (MemLp.coeFn_toLp hx0)
      have hv_ae :
          (fun z : (Fin n → ℝ) => v z) =ᵐ[(volume : Measure (Fin n → ℝ))]
            (eigenfunctionProd (n := n) ξ krest) := by
        simpa [v] using (MemLp.coeFn_toLp hH)
      have huv :
          ⟪u, v⟫_ℝ =
            ∫ z : (Fin n → ℝ),
              gz z * eigenfunctionProd (n := n) ξ krest z
                ∂(volume : Measure (Fin n → ℝ)) := by
        rw [MeasureTheory.L2.inner_def]
        have hAe :
            (fun z : (Fin n → ℝ) => ⟪u z, v z⟫_ℝ)
              =ᵐ[(volume : Measure (Fin n → ℝ))]
                fun z : (Fin n → ℝ) =>
                  (eigenfunctionProd (n := n) ξ krest z) * (gz z) := by
          filter_upwards [hu_ae, hv_ae] with z huz hvz
          simp [huz, hvz]
        have :
            (∫ z : (Fin n → ℝ), ⟪u z, v z⟫_ℝ ∂(volume : Measure (Fin n → ℝ)))
              =
            ∫ z : (Fin n → ℝ),
              (eigenfunctionProd (n := n) ξ krest z) * (gz z)
                ∂(volume : Measure (Fin n → ℝ)) := by
          simpa using
            (MeasureTheory.integral_congr_ae (μ := (volume : Measure (Fin n → ℝ))) hAe)
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have huu :
          ⟪u, u⟫_ℝ =
            ∫ z : (Fin n → ℝ), (gz z) ^ 2 ∂(volume : Measure (Fin n → ℝ)) := by
        rw [MeasureTheory.L2.inner_def]
        have hAe :
            (fun z : (Fin n → ℝ) => ⟪u z, u z⟫_ℝ)
              =ᵐ[(volume : Measure (Fin n → ℝ))] fun z => (gz z) ^ 2 := by
          filter_upwards [hu_ae] with z huz
          simp [huz]
        simpa using
          (MeasureTheory.integral_congr_ae (μ := (volume : Measure (Fin n → ℝ))) hAe)
      have hvv : ⟪v, v⟫_ℝ = C := by
        rw [MeasureTheory.L2.inner_def]
        have hAe :
            (fun z : (Fin n → ℝ) => ⟪v z, v z⟫_ℝ)
              =ᵐ[(volume : Measure (Fin n → ℝ))]
                fun z => (eigenfunctionProd (n := n) ξ krest z) ^ 2 := by
          filter_upwards [hv_ae] with z hvz
          have ht : ∀ t : ℝ, ⟪t, t⟫_ℝ = t ^ 2 := by
            intro t
            simp
          simpa [hvz] using ht (eigenfunctionProd (n := n) ξ krest z)
        have :
            (∫ z : (Fin n → ℝ), ⟪v z, v z⟫_ℝ ∂(volume : Measure (Fin n → ℝ)))
              =
            ∫ z : (Fin n → ℝ), (eigenfunctionProd (n := n) ξ krest z) ^ 2
                ∂(volume : Measure (Fin n → ℝ)) := by
          simpa using
            (MeasureTheory.integral_congr_ae (μ := (volume : Measure (Fin n → ℝ))) hAe)
        simpa [C] using this
      have hcs : ⟪u, v⟫_ℝ * ⟪u, v⟫_ℝ ≤ ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ :=
        real_inner_mul_inner_self_le u v
      have hcs' := hcs
      rw [huv] at hcs'
      rw [huu] at hcs'
      rw [hvv] at hcs'
      exact hcs'
    simpa [F, C, gz, pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner
  have hdom_int :
      Integrable
        (fun x0 : ℝ =>
          C * (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))))
        (volume : Measure ℝ) :=
    hG2_int.const_mul C
  have hF2_meas : AEStronglyMeasurable (fun x0 : ℝ => (F x0) ^ 2) (volume : Measure ℝ) := by
    simpa [pow_two] using (hF_meas.mul hF_meas)
  have hF2_int :
      Integrable (fun x0 : ℝ => (F x0) ^ 2) (volume : Measure ℝ) := by
    refine hdom_int.mono hF2_meas ?_
    filter_upwards [hbound] with x0 hx0
    have hL : 0 ≤ (F x0) ^ 2 := sq_nonneg _
    have hI :
        0 ≤ (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) := by
      refine integral_nonneg ?_
      intro z
      exact sq_nonneg _
    have hR :
        0 ≤ C * (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) := by
      exact mul_nonneg hC_nonneg hI
    have hCabs : |C| = C := abs_of_nonneg hC_nonneg
    have hIabs :
        |∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))| =
          ∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ)) := by
      exact abs_of_nonneg hI
    simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR, abs_mul, hCabs, hIabs] using hx0
  have hF_memLp : MemLp F 2 (volume : Measure ℝ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hF_meas).2 hF2_int
  simpa [F] using hF_memLp

private lemma integral_coeffFun_mul_eigenfunctionReal_eq_zero_of_prod_orthogonality
    {n : ℕ} {ξ : ℝ} (hξ : ξ ≠ 0)
    (e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)))
    (hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
      (volume : Measure (ℝ × (Fin n → ℝ))))
    (he : e = MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
    {g : (Fin (n + 1) → ℝ) → ℝ} {g' : (ℝ × (Fin n → ℝ)) → ℝ}
    (hg'_def : g' = fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y))
    (hg'_memLp : MemLp g' 2 (volume : Measure (ℝ × (Fin n → ℝ))))
    (horth : ∀ k : Fin (n + 1) → ℕ,
      ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x = 0)
    (krest : Fin n → ℕ) (k0 : ℕ) :
    (∫ x0 : ℝ,
      (∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
        ∂(volume : Measure (Fin n → ℝ))) * eigenfunctionReal ξ k0 x0
        ∂(volume : Measure ℝ)) = 0 := by
  let F : ℝ → ℝ :=
    fun x0 =>
      ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
        ∂(volume : Measure (Fin n → ℝ))
  let k : Fin (n + 1) → ℕ := Fin.cons k0 krest
  have hk : (∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x) = 0 :=
    horth k
  have hk' :
      (∫ y : (ℝ × (Fin n → ℝ)),
          g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)) = 0 := by
    exact
      integral_eq_zero_on_prod_of_integral_eq_zero_on_piFinSuccAbove
        (n := n) (ξ := ξ) e hmp (g := g) (g' := g') hg'_def k hk
  have hk'' :
      (∫ y : (ℝ × (Fin n → ℝ)),
          g' y *
            (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)) = 0 := by
    have hprod :
        (fun y : (ℝ × (Fin n → ℝ)) =>
            eigenfunctionProd (n := n + 1) ξ k (e.symm y)) =
          fun y : (ℝ × (Fin n → ℝ)) =>
            eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2 := by
      funext y
      simp [eigenfunctionProd, k, Fin.prod_univ_succ,
        he, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ, Fin.cons_zero]
    have hAe :
        (fun y : (ℝ × (Fin n → ℝ)) =>
            g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y))
          =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))]
            fun y : (ℝ × (Fin n → ℝ)) =>
              g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2) := by
      refine Filter.Eventually.of_forall ?_
      intro y
      have hy :
          eigenfunctionProd (n := n + 1) ξ k (e.symm y) =
            eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2 := by
        simpa using congrArg (fun f => f y) hprod
      change
        g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y) =
          g' y *
            (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
      rw [hy]
    have hInt :
        (∫ y : (ℝ × (Fin n → ℝ)),
              g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)
                ∂(volume : Measure (ℝ × (Fin n → ℝ))))
          =
        ∫ y : (ℝ × (Fin n → ℝ)),
              g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
                ∂(volume : Measure (ℝ × (Fin n → ℝ))) := by
      simpa using
        (MeasureTheory.integral_congr_ae (μ := (volume : Measure (ℝ × (Fin n → ℝ)))) hAe)
    calc
      (∫ y : (ℝ × (Fin n → ℝ)),
            g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
              ∂(volume : Measure (ℝ × (Fin n → ℝ))))
          =
        ∫ y : (ℝ × (Fin n → ℝ)),
              g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)
                ∂(volume : Measure (ℝ × (Fin n → ℝ))) := by
          simpa using hInt.symm
      _ = 0 := hk'
  have h_int :
      Integrable
        (fun y : (ℝ × (Fin n → ℝ)) =>
          g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2))
        (volume : Measure (ℝ × (Fin n → ℝ))) := by
    have hH :
        MemLp (fun y : (ℝ × (Fin n → ℝ)) =>
            eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
          2 (volume : Measure (ℝ × (Fin n → ℝ))) := by
      have hmeas :
          AEStronglyMeasurable
            (fun y : (ℝ × (Fin n → ℝ)) =>
              eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
            (volume : Measure (ℝ × (Fin n → ℝ))) := by
        have h1 :
            AEStronglyMeasurable (fun y : (ℝ × (Fin n → ℝ)) => eigenfunctionReal ξ k0 y.1)
              (volume : Measure (ℝ × (Fin n → ℝ))) := by
          have hcont : Continuous (eigenfunctionReal ξ k0) :=
            HarmonicOscillator.continuous_eigenfunctionReal (ξ := ξ) (hξ := hξ) (n := k0)
          have hmeas1 :
              AEStronglyMeasurable (fun t : ℝ => eigenfunctionReal ξ k0 t)
                (volume : Measure ℝ) :=
            hcont.aestronglyMeasurable
          exact hmeas1.comp_quasiMeasurePreserving
            (by
              simpa using
                (MeasureTheory.Measure.quasiMeasurePreserving_fst
                  (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))))
        have h2 :
            AEStronglyMeasurable
              (fun y : (ℝ × (Fin n → ℝ)) => eigenfunctionProd (n := n) ξ krest y.2)
              (volume : Measure (ℝ × (Fin n → ℝ))) := by
          have hmeas2 :
              AEStronglyMeasurable (eigenfunctionProd (n := n) ξ krest)
                (volume : Measure (Fin n → ℝ)) :=
            aestronglyMeasurable_eigenfunctionProd
              (n := n) (ξ := ξ) (hξ := hξ)
              krest
          exact hmeas2.comp_quasiMeasurePreserving
            (by
              simpa using
                (MeasureTheory.Measure.quasiMeasurePreserving_snd
                  (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))))
        exact h1.mul h2
      have hint :
          Integrable
            (fun y : (ℝ × (Fin n → ℝ)) =>
              (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2) ^ 2)
            (volume : Measure (ℝ × (Fin n → ℝ))) := by
        have h1 :
            Integrable (fun x0 : ℝ => (eigenfunctionReal ξ k0 x0) ^ 2)
              (volume : Measure ℝ) := by
          simpa using
            (HarmonicOscillator.integrable_eigenfunctionReal_sq
              (ξ := ξ) (hξ := hξ)
              (n := k0))
        have h2 :
            Integrable (fun z : (Fin n → ℝ) => (eigenfunctionProd (n := n) ξ krest z) ^ 2)
              (volume : Measure (Fin n → ℝ)) := by
          simpa using
            integrable_eigenfunctionProd_sq (n := n) (ξ := ξ) (hξ := hξ) krest
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, mul_pow] using
          (MeasureTheory.Integrable.mul_prod (μ := (volume : Measure ℝ))
            (ν := (volume : Measure (Fin n → ℝ)))
            (f := fun x0 : ℝ => (eigenfunctionReal ξ k0 x0) ^ 2)
            (g := fun z : (Fin n → ℝ) => (eigenfunctionProd (n := n) ξ krest z) ^ 2)
            h1 h2)
      exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hint
    exact MeasureTheory.MemLp.integrable_mul hg'_memLp hH
  have hfub :
      (∫ y : (ℝ × (Fin n → ℝ)),
          g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2))
        =
      ∫ x0 : ℝ,
        ∫ z : (Fin n → ℝ),
          g' (x0, z) * (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
          ∂(volume : Measure (Fin n → ℝ))
        ∂(volume : Measure ℝ) := by
    simpa using
      (MeasureTheory.integral_prod
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
        (f := fun y : (ℝ × (Fin n → ℝ)) =>
          g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2))
        h_int)
  have hfub' :
      (∫ x0 : ℝ,
        ∫ z : (Fin n → ℝ),
          g' (x0, z) * (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
          ∂(volume : Measure (Fin n → ℝ))
        ∂(volume : Measure ℝ))
        =
      ∫ x0 : ℝ, (F x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ) := by
    refine integral_congr_ae ?_
    filter_upwards with x0
    have hinner :
        (∫ z : (Fin n → ℝ),
              g' (x0, z) *
                (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                ∂(volume : Measure (Fin n → ℝ)))
          =
        (∫ z : (Fin n → ℝ),
              g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
                ∂(volume : Measure (Fin n → ℝ))) * eigenfunctionReal ξ k0 x0 := by
      have hAe :
          (fun z : (Fin n → ℝ) =>
              g' (x0, z) *
                (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z))
            =ᵐ[(volume : Measure (Fin n → ℝ))]
              fun z : (Fin n → ℝ) =>
                (g' (x0, z) * eigenfunctionProd (n := n) ξ krest z) * eigenfunctionReal ξ k0 x0 := by
        refine Filter.Eventually.of_forall ?_
        intro z
        ring
      calc
        (∫ z : (Fin n → ℝ),
              g' (x0, z) *
                (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                ∂(volume : Measure (Fin n → ℝ)))
            =
          ∫ z : (Fin n → ℝ),
              (g' (x0, z) * eigenfunctionProd (n := n) ξ krest z) * eigenfunctionReal ξ k0 x0
                ∂(volume : Measure (Fin n → ℝ)) := by
          simpa using
            (MeasureTheory.integral_congr_ae (μ := (volume : Measure (Fin n → ℝ))) hAe)
        _ =
          (∫ z : (Fin n → ℝ),
                g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
                  ∂(volume : Measure (Fin n → ℝ))) * eigenfunctionReal ξ k0 x0 := by
          simpa using
            (MeasureTheory.integral_mul_const
              (μ := (volume : Measure (Fin n → ℝ))) (eigenfunctionReal ξ k0 x0)
              (fun z : (Fin n → ℝ) => g' (x0, z) * eigenfunctionProd (n := n) ξ krest z))
    dsimp [F]
    exact hinner
  have : ∫ x0 : ℝ, (F x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ) = 0 := by
    have hk_fub :
        (∫ x0 : ℝ,
              ∫ z : (Fin n → ℝ),
                g' (x0, z) *
                  (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                  ∂(volume : Measure (Fin n → ℝ))
              ∂(volume : Measure ℝ)) = 0 := by
      calc
        (∫ x0 : ℝ,
              ∫ z : (Fin n → ℝ),
                g' (x0, z) *
                  (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                  ∂(volume : Measure (Fin n → ℝ))
              ∂(volume : Measure ℝ))
            =
          (∫ y : (ℝ × (Fin n → ℝ)),
              g' y *
                (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
                ∂(volume : Measure (ℝ × (Fin n → ℝ)))) := by
          simpa using hfub.symm
        _ = 0 := hk''
    calc
      (∫ x0 : ℝ, (F x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ))
          =
        (∫ x0 : ℝ,
              ∫ z : (Fin n → ℝ),
                g' (x0, z) *
                  (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                  ∂(volume : Measure (Fin n → ℝ))
              ∂(volume : Measure ℝ)) := by
          simpa using hfub'.symm
      _ = 0 := hk_fub
  simpa [F, mul_comm] using this

private lemma ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero_succ
    (n : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (ih : ∀ {g : (Fin n → ℝ) → ℝ},
      MemLp g 2 (volume : Measure (Fin n → ℝ)) →
      (∀ k : Fin n → ℕ,
        ∫ x : (Fin n → ℝ), g x * eigenfunctionProd (n := n) ξ k x = 0) →
      g =ᵐ[(volume : Measure (Fin n → ℝ))] 0)
    {g : (Fin (n + 1) → ℝ) → ℝ}
    (hg : MemLp g 2 (volume : Measure (Fin (n + 1) → ℝ)))
    (horth : ∀ k : Fin (n + 1) → ℕ,
      ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x = 0) :
    g =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] 0 := by
  classical
  let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp :
      MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        (volume : Measure (ℝ × (Fin n → ℝ))) := by
    simpa [e] using
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
  let g' : (ℝ × (Fin n → ℝ)) → ℝ := fun y => g (e.symm y)
  have hg' : MemLp g' 2 (volume : Measure (ℝ × (Fin n → ℝ))) := by
    simpa [g'] using (hg.comp_measurePreserving hmp.symm)
  let F (krest : Fin n → ℕ) : ℝ → ℝ :=
    fun x0 =>
      ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
        ∂(volume : Measure (Fin n → ℝ))
  have hF_memLp : ∀ krest : Fin n → ℕ, MemLp (F krest) 2 (volume : Measure ℝ) := by
    intro krest
    simpa [F] using
      memLp_coeffFun_of_memLp_prod
        (n := n) (ξ := ξ) (hξ := hξ) (g' := g') hg' krest
  have hF_orth :
      ∀ krest : Fin n → ℕ, ∀ k0 : ℕ,
        ∫ x0 : ℝ, (F krest x0) * eigenfunctionReal ξ k0 x0 = 0 := by
    intro krest k0
    have hg'_def : g' = fun y : (ℝ × (Fin n → ℝ)) => g (e.symm y) := rfl
    simpa [F] using
      integral_coeffFun_mul_eigenfunctionReal_eq_zero_of_prod_orthogonality
        (n := n) (ξ := ξ) (hξ := hξ) e hmp (he := rfl)
        (g := g) (g' := g') hg'_def hg' horth krest k0
  have hF_zero :
      ∀ krest : Fin n → ℕ, (F krest) =ᵐ[(volume : Measure ℝ)] 0 := by
    exact
      ae_coeffFun_zero_of_forall_integral_eigenfunctionReal_eq_zero
        (ξ := ξ) hξ (F := F) hF_memLp hF_orth
  haveI : Countable (Fin n → ℕ) := by infer_instance
  have hF_zero_all :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ), ∀ krest : Fin n → ℕ, F krest x0 = 0 := by
    exact
      ae_all_eq_zero_of_forall_ae_eq_zero
        (μ := (volume : Measure ℝ)) (f := fun x0 krest => F krest x0) hF_zero
  have hslice_memLp :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        MemLp (fun z : (Fin n → ℝ) => g' (x0, z)) 2
          (volume : Measure (Fin n → ℝ)) :=
    ae_memLp_two_slice_of_memLp_two_prod (n := n) (g := g') hg'
  have horth_ae :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        ∀ krest : Fin n → ℕ,
          ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z = 0 := by
    filter_upwards [hF_zero_all] with x0 hcoeff0 krest
    simpa [F] using hcoeff0 krest
  have hslice_zero :
      ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
        (fun z : (Fin n → ℝ) => g' (x0, z)) =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
    exact
      ae_slice_zero_of_ae_memLp_and_ae_orthogonality
        (ih := ih) (ξ := ξ) (g := g') hslice_memLp horth_ae
  have hg'_ae0 : g' =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] 0 :=
    ae_eq_zero_of_ae_slice_eq_zero (n := n) (g := g') hg' hslice_zero
  exact ae_eq_zero_of_comp_piFinSuccAbove (n := n) e hmp (by simpa [g'] using hg'_ae0)

/-- Completeness of the product eigenfunctions on `Fin n → ℝ`:
if `g ∈ L²` is orthogonal to all products `∏ i, eigenfunctionReal ξ (k i) (x i)`, then `g = 0` a.e. -/
theorem ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero
    (n : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) {g : (Fin n → ℝ) → ℝ}
    (hg : MemLp g 2 (volume : Measure (Fin n → ℝ)))
    (horth : ∀ k : Fin n → ℕ,
      ∫ x : (Fin n → ℝ), g x * eigenfunctionProd (n := n) ξ k x = 0) :
    g =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
  classical
  induction n with
  | zero =>
      exact ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero_zero (ξ := ξ) horth
  | succ n ih =>
      exact
        ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero_succ
          (n := n) (ξ := ξ) (hξ := hξ) (ih := ih) (g := g) hg horth

end SpaceTimeHermite

end

end PhysLean
