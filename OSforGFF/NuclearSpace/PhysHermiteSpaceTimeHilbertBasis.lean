/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

import OSforGFF.NuclearSpace.PhysHermiteSpaceTimePiCompleteness
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffs

/-!
# Hilbert basis on `L²(SpaceTime)` from spacetime Hermite eigenfunctions

We package the normalized spacetime harmonic-oscillator eigenfunctions
`normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ : ℕ → SpaceTime →₂[volume] ℝ`
as a `HilbertBasis ℕ ℝ (L²(SpaceTime))`.

The analytic core is the completeness theorem on the product model `Fin 4 → ℝ`
(`ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero`) and the measure-preserving
identification `WithLp.toLp`.
We then derive Parseval/Plancherel identities for the coefficient sequence `normalizedCoeffL2`.
-/

open scoped BigOperators ENNReal RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory

namespace SpaceTimeHermite

open scoped InnerProductSpace

local notation "SpaceTimeL2" => (SpaceTime →₂[(volume : Measure SpaceTime)] ℝ)

/-! ## Completeness of the normalized spacetime eigenfunctions -/

private lemma eigenfunctionRealSpaceTime_comp_toLp_eq_eigenfunctionProd
    (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (v : Fin STDimension → ℝ) :
    eigenfunctionRealSpaceTime ξ hξ n (WithLp.toLp (2 : ℝ≥0∞) v) =
      eigenfunctionProd (n := STDimension) ξ (idx n) v := by
  simp [eigenfunctionRealSpaceTime_eq_prod, eigenfunctionProd, eigenfunctionRealSchwartz_apply]

private lemma normalizedEigenfunctionSpaceTimeL2_inner_eq_zero_of_mem_orthogonal
    (ξ : ℝ) (hξ : ξ ≠ 0) {g : SpaceTimeL2}
    (hg : g ∈ (Submodule.span ℝ (Set.range (normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)))ᗮ) :
    ∀ n : ℕ, ⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n, g⟫ = 0 := by
  intro n
  have hn_mem :
      normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n ∈
        Submodule.span ℝ (Set.range (normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)) := by
    exact Submodule.subset_span ⟨n, rfl⟩
  exact (Submodule.mem_orthogonal
      (K := Submodule.span ℝ (Set.range (normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ))) g).1 hg _ hn_mem

private lemma ae_eq_zero_of_forall_integral_eigenfunctionRealSpaceTime_eq_zero
    (ξ : ℝ) (hξ : ξ ≠ 0) {g : SpaceTime → ℝ}
    (hg : MemLp g 2 (volume : Measure SpaceTime))
    (horth : ∀ n : ℕ, ∫ x : SpaceTime, g x * eigenfunctionRealSpaceTime ξ hξ n x = 0) :
    g =ᵐ[(volume : Measure SpaceTime)] 0 := by
  let e : (Fin STDimension → ℝ) → SpaceTime := WithLp.toLp (2 : ℝ≥0∞)
  have hmp : MeasurePreserving e (volume : Measure (Fin STDimension → ℝ)) (volume : Measure SpaceTime) :=
    PiLp.volume_preserving_toLp (Fin STDimension)
  let g' : (Fin STDimension → ℝ) → ℝ := fun v => g (e v)
  have hg' : MemLp g' 2 (volume : Measure (Fin STDimension → ℝ)) := by
    simpa [g'] using (hg.comp_measurePreserving hmp)
  have horth' : ∀ k : Fin STDimension → ℕ,
      ∫ v : (Fin STDimension → ℝ), g' v * eigenfunctionProd (n := STDimension) ξ k v = 0 := by
    intro k
    rcases exists_idx_eq k with ⟨n, hidx⟩
    have hk0 : ∫ x : SpaceTime, g x * eigenfunctionRealSpaceTime ξ hξ n x = 0 := horth n
    -- Change variables along `e` to rewrite the spacetime integral as a product integral.
    have hk_comp :
        (∫ v : (Fin STDimension → ℝ),
            (fun x : SpaceTime => g x * eigenfunctionRealSpaceTime ξ hξ n x) (e v)
              ∂(volume : Measure (Fin STDimension → ℝ)))
          =
        ∫ x : SpaceTime, g x * eigenfunctionRealSpaceTime ξ hξ n x ∂(volume : Measure SpaceTime) := by
      simpa using
        (hmp.integral_comp
          (MeasurableEquiv.toLp (2 : ℝ≥0∞) (Fin STDimension → ℝ)).measurableEmbedding
          (g := fun x : SpaceTime => g x * eigenfunctionRealSpaceTime ξ hξ n x))
    have hk1 :
        (∫ v : (Fin STDimension → ℝ),
            g' v * eigenfunctionRealSpaceTime ξ hξ n (e v) ∂(volume : Measure (Fin STDimension → ℝ)))
          = 0 := by
      have hk1' :
          (∫ v : (Fin STDimension → ℝ),
              g' v * eigenfunctionRealSpaceTime ξ hξ n (e v)
                ∂(volume : Measure (Fin STDimension → ℝ)))
            =
          ∫ x : SpaceTime, g x * eigenfunctionRealSpaceTime ξ hξ n x
                ∂(volume : Measure SpaceTime) := by
        simpa [g', e] using hk_comp
      simpa [hk1'] using hk0
    have hprod :
        (fun v : (Fin STDimension → ℝ) =>
            eigenfunctionRealSpaceTime ξ hξ n (e v))
          =
        fun v : (Fin STDimension → ℝ) =>
            eigenfunctionProd (n := STDimension) ξ k v := by
      funext v
      have : eigenfunctionRealSpaceTime ξ hξ n (e v) =
          eigenfunctionProd (n := STDimension) ξ (idx n) v := by
        simpa [e] using
          (eigenfunctionRealSpaceTime_comp_toLp_eq_eigenfunctionProd
            (ξ := ξ) (hξ := hξ) (n := n) (v := v))
      simpa [hidx] using this
    have hk2 : (∫ v : (Fin STDimension → ℝ),
            g' v * eigenfunctionProd (n := STDimension) ξ k v ∂(volume : Measure (Fin STDimension → ℝ)))
          = ∫ v : (Fin STDimension → ℝ),
            g' v * eigenfunctionRealSpaceTime ξ hξ n (e v) ∂(volume : Measure (Fin STDimension → ℝ)) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro v
      have : eigenfunctionRealSpaceTime ξ hξ n (e v) = eigenfunctionProd (n := STDimension) ξ k v := by
        simpa using congrArg (fun f => f v) hprod
      simp [this, mul_comm]
    exact hk2.trans hk1
  have hzero' :
      g' =ᵐ[(volume : Measure (Fin STDimension → ℝ))] 0 := by
    simpa using
      (ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero
        (n := STDimension) (ξ := ξ) (hξ := hξ) (g := g') hg' horth')
  -- Transport back to `SpaceTime` along `ofLp`.
  let eInv : SpaceTime → (Fin STDimension → ℝ) := WithLp.ofLp
  have hmpInv : MeasurePreserving eInv (volume : Measure SpaceTime) (volume : Measure (Fin STDimension → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin STDimension)
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving eInv
      (volume : Measure SpaceTime) (volume : Measure (Fin STDimension → ℝ)) :=
    hmpInv.quasiMeasurePreserving
  have hcomp : g' ∘ eInv =ᵐ[(volume : Measure SpaceTime)] 0 := by
    have hcomp' :
        g' ∘ eInv =ᵐ[(volume : Measure SpaceTime)]
          (0 : (Fin STDimension → ℝ) → ℝ) ∘ eInv :=
      hq.ae_eq_comp hzero'
    simpa using hcomp'
  have hge : g' ∘ eInv =ᵐ[(volume : Measure SpaceTime)] g := by
    refine Filter.Eventually.of_forall ?_
    intro x
    dsimp [g', eInv, e]
  exact hge.symm.trans hcomp

theorem span_normalizedEigenfunctionSpaceTimeL2_orthogonal_eq_bot (ξ : ℝ) (hξ : ξ ≠ 0) :
    (Submodule.span ℝ (Set.range (normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  intro g hg
  have hinner0 :
      ∀ n : ℕ, ⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n, g⟫ = 0 :=
    normalizedEigenfunctionSpaceTimeL2_inner_eq_zero_of_mem_orthogonal (ξ := ξ) (hξ := hξ) (hg := hg)
  have horth_int : ∀ n : ℕ, ∫ x : SpaceTime, (g x) * eigenfunctionRealSpaceTime ξ hξ n x = 0 := by
    intro n
    have h0 : (⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n, g⟫ : ℝ) = 0 := hinner0 n
    have hsc :
        (Real.sqrt (normConstSpaceTime ξ n))⁻¹ *
            ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, g⟫ = 0 := by
      simpa [normalizedEigenfunctionSpaceTimeL2, inner_smul_left, mul_assoc] using h0
    have hsqrt_ne : (Real.sqrt (normConstSpaceTime ξ n)) ≠ 0 := by
      have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
      exact (Real.sqrt_ne_zero').2 hpos
    have hinner : ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, g⟫ = 0 := by
      have ha : (Real.sqrt (normConstSpaceTime ξ n))⁻¹ ≠ 0 := inv_ne_zero hsqrt_ne
      exact (mul_eq_zero.mp hsc).resolve_left ha
    have hintegral :
        ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, g⟫ =
          ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * g x
            ∂(volume : Measure SpaceTime) := by

      simp only [eigenfunctionRealSpaceTimeL2, MeasureTheory.L2.inner_def]
      refine MeasureTheory.integral_congr_ae ?_
      have hn_ae :
          (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp
              (eigenfunctionRealSpaceTime ξ hξ n) =ᵐ[(volume : Measure SpaceTime)]
            eigenfunctionRealSpaceTime ξ hξ n :=
        (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).coeFn_toLp
      filter_upwards [hn_ae] with x hx
      simp [hx, mul_comm]
    have : (∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * g x
            ∂(volume : Measure SpaceTime)) = 0 := by
      simpa [hintegral] using hinner
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hg_fun : MemLp (fun x : SpaceTime => g x) 2 (volume : Measure SpaceTime) := by
    exact (Lp.memLp g)
  have hzero : (fun x : SpaceTime => g x) =ᵐ[(volume : Measure SpaceTime)] 0 := by
    refine ae_eq_zero_of_forall_integral_eigenfunctionRealSpaceTime_eq_zero
      (ξ := ξ) (hξ := hξ) (g := fun x => g x) hg_fun horth_int
  apply Lp.ext
  have hz : ((0 : SpaceTimeL2) : SpaceTime → ℝ) =ᵐ[(volume : Measure SpaceTime)] 0 := by
    simpa using (Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure SpaceTime)))
  exact hzero.trans hz.symm

/-- The normalized spacetime eigenfunctions form a Hilbert basis of `L²(SpaceTime)`. -/
noncomputable def normalizedEigenfunctionSpaceTimeHilbertBasis (ξ : ℝ) (hξ : ξ ≠ 0) :
    HilbertBasis ℕ ℝ SpaceTimeL2 :=
  HilbertBasis.mkOfOrthogonalEqBot
    (v := normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)
    (orthonormal_normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)
    (span_normalizedEigenfunctionSpaceTimeL2_orthogonal_eq_bot (ξ := ξ) (hξ := hξ))

@[simp]
theorem normalizedEigenfunctionSpaceTimeHilbertBasis_coe (ξ : ℝ) (hξ : ξ ≠ 0) :
    (normalizedEigenfunctionSpaceTimeHilbertBasis (ξ := ξ) hξ : ℕ → SpaceTimeL2) =
      normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ := by
  simp [normalizedEigenfunctionSpaceTimeHilbertBasis]

/-! ## Parseval for `normalizedCoeffL2` -/

/-- Parseval identity for the normalized coefficient sequence of `f : TestFunction`. -/
theorem norm_normalizedCoeffL2_eq_norm_toLp (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    ‖normalizedCoeffL2 ξ hξ f‖ = ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
  let b : HilbertBasis ℕ ℝ SpaceTimeL2 := normalizedEigenfunctionSpaceTimeHilbertBasis (ξ := ξ) hξ
  have hrepr :  ‖b.repr (f.toLp 2 (volume : Measure SpaceTime))‖ = ‖f.toLp 2 (volume : Measure SpaceTime)‖ := by
    simp
  have hcoeff :
      b.repr (f.toLp 2 (volume : Measure SpaceTime)) = normalizedCoeffL2 ξ hξ f := by
    ext n
    have hL : b.repr (f.toLp 2 (volume : Measure SpaceTime)) n =
        ⟪b n, f.toLp 2 (volume : Measure SpaceTime)⟫ := by
      simpa using (HilbertBasis.repr_apply_apply b (f.toLp 2 (volume : Measure SpaceTime)) n)
    have hb : (b n) = normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n := by
      aesop
    have hR : (normalizedCoeffL2 ξ hξ f : ℕ → ℝ) n =
        ⟪b n, f.toLp 2 (volume : Measure SpaceTime)⟫ := by
      simpa [hb] using (normalizedCoeffL2_apply_eq_inner (ξ := ξ) (hξ := hξ) (f := f) (n := n))
    exact hL.trans hR.symm
  simpa [hcoeff] using hrepr

end SpaceTimeHermite

end

end PhysLean
