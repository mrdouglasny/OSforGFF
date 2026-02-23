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

/-- Completeness of the product eigenfunctions on `Fin n → ℝ`:
if `g ∈ L²` is orthogonal to all products `∏ i, eigenfunctionReal ξ (k i) (x i)`, then `g = 0` a.e. -/
theorem ae_eq_zero_of_forall_integral_eigenfunctionProd_eq_zero
    (n : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) {g : (Fin n → ℝ) → ℝ}
    (hg : MemLp g 2 (volume : Measure (Fin n → ℝ)))
    (horth : ∀ k : Fin n → ℕ,
      ∫ x : (Fin n → ℝ), g x * eigenfunctionProd (n := n) ξ k x = 0) :
    g =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
  classical
  -- We prove this by induction on `n`, peeling off one coordinate at a time.
  induction n with
  | zero =>
      -- On the empty product, every function is constant; use the Dirac description of `volume`.
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
      -- hence `g` is identically zero (the domain is a subsingleton)
      have hg0 : g = 0 := by
        funext x
        have : x = x0 := Subsingleton.elim x x0
        simpa [this, hgx0]
      simpa [hg0]
  | succ n ih =>
      -- Split off coordinate `0` using `piFinSuccAbove`.
      let e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      have hmp :
          MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
            (volume : Measure (ℝ × (Fin n → ℝ))) := by
        simpa [e] using
          (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      -- Transport `g` to the product model.
      let g' : (ℝ × (Fin n → ℝ)) → ℝ := fun y => g (e.symm y)
      have hg' : MemLp g' 2 (volume : Measure (ℝ × (Fin n → ℝ))) := by
        simpa [g'] using (hg.comp_measurePreserving hmp.symm)
      -- For each remaining multi-index, define the coefficient function in the first coordinate.
      let F (krest : Fin n → ℕ) : ℝ → ℝ :=
        fun x0 =>
          ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z
            ∂(volume : Measure (Fin n → ℝ))
      -- `F krest` is `L²` on `ℝ`, with a Cauchy–Schwarz estimate.
      have hF_memLp : ∀ krest : Fin n → ℕ, MemLp (F krest) 2 (volume : Measure ℝ) := by
        intro krest
        -- measurability
        have hH_meas_prod :
            AEStronglyMeasurable
              (fun p : ℝ × (Fin n → ℝ) => eigenfunctionProd (n := n) ξ krest p.2)
              (volume : Measure (ℝ × (Fin n → ℝ))) := by
          have hH_meas :
              AEStronglyMeasurable (eigenfunctionProd (n := n) ξ krest)
                (volume : Measure (Fin n → ℝ)) :=
            aestronglyMeasurable_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) krest
          -- compose with `snd`
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
        have hF_meas : AEStronglyMeasurable (F krest) (volume : Measure ℝ) := by
          simpa [F] using
            (MeasureTheory.AEStronglyMeasurable.integral_prod_right'
              (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))) h_integrand_meas)
        -- integrability of `g'^2` on the product
        have hgsq_int :
            Integrable (fun p : ℝ × (Fin n → ℝ) => (g' p) ^ 2)
              (volume : Measure (ℝ × (Fin n → ℝ))) :=
          MeasureTheory.MemLp.integrable_sq hg'
        -- a.e. slice `MemLp` for `x0 ↦ g' (x0, ·)` in the second variable
        have hslice_memLp :
            ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
              MemLp (fun z : (Fin n → ℝ) => g' (x0, z)) 2 (volume : Measure (Fin n → ℝ)) := by
          have hslice_meas :
              ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
                AEStronglyMeasurable (fun z : (Fin n → ℝ) => g' (x0, z))
                  (volume : Measure (Fin n → ℝ)) := by
            simpa using (hg'.1.prodMk_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
          have hslice_sq_int :
              ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
                Integrable (fun z : (Fin n → ℝ) => (g' (x0, z)) ^ 2)
                  (volume : Measure (Fin n → ℝ)) := by
            simpa using hgsq_int.prod_right_ae
          filter_upwards [hslice_meas, hslice_sq_int] with x0 hmeas hint
          exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hint
        -- Constant `C = ∫ (eigenfunctionProd krest)^2`.
        let C : ℝ :=
          ∫ z : (Fin n → ℝ), (eigenfunctionProd (n := n) ξ krest z) ^ 2 ∂(volume : Measure (Fin n → ℝ))
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
        -- a.e. bound `F^2 ≤ C * ∫ g'^2`
        have hbound :
            (fun x0 : ℝ => (F krest x0) ^ 2) ≤ᵐ[(volume : Measure ℝ)]
              fun x0 : ℝ =>
                C * (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) := by
          filter_upwards [hslice_memLp] with x0 hx0
          -- Cauchy–Schwarz on `L²(volume)` in the `z`-variable.
          let gz : (Fin n → ℝ) → ℝ := fun z => g' (x0, z)
          have hH : MemLp (eigenfunctionProd (n := n) ξ krest) 2 (volume : Measure (Fin n → ℝ)) :=
            memLp_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) krest
          -- rewrite the coefficient as an `L²` inner product and apply `real_inner_mul_inner_self_le`.
          have hinner :
              (∫ z : (Fin n → ℝ), gz z * eigenfunctionProd (n := n) ξ krest z
                  ∂(volume : Measure (Fin n → ℝ)))
                *
              (∫ z : (Fin n → ℝ), gz z * eigenfunctionProd (n := n) ξ krest z
                  ∂(volume : Measure (Fin n → ℝ)))
                ≤
              (∫ z : (Fin n → ℝ), (gz z) ^ 2 ∂(volume : Measure (Fin n → ℝ))) * C := by
            -- use the Cauchy–Schwarz inequality in `L²`
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
                -- avoid unfolding `eigenfunctionProd` (simp will otherwise introduce `abs`)
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
            -- rewrite the inner products using the explicit integral identities
            have hcs' := hcs
            rw [huv] at hcs'
            rw [huu] at hcs'
            rw [hvv] at hcs'
            exact hcs'
          -- translate into the `F` notation (and use `pow_two`)
          -- `F krest x0` is the coefficient integral
          simpa [F, C, gz, pow_two, mul_assoc, mul_comm, mul_left_comm] using hinner
        -- show integrability of `F^2` by domination
        have hdom_int :
            Integrable
              (fun x0 : ℝ =>
                C * (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))))
              (volume : Measure ℝ) :=
          hG2_int.const_mul C
        have hF2_meas : AEStronglyMeasurable (fun x0 : ℝ => (F krest x0) ^ 2) (volume : Measure ℝ) := by
          -- `x ↦ (F x)^2` is measurable since `F` is.
          simpa [pow_two] using (hF_meas.mul hF_meas)
        have hF2_int :
            Integrable (fun x0 : ℝ => (F krest x0) ^ 2) (volume : Measure ℝ) := by
          refine hdom_int.mono hF2_meas ?_
          filter_upwards [hbound] with x0 hx0
          have hL : 0 ≤ (F krest x0) ^ 2 := sq_nonneg _
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
          -- rewrite norms/abs and use the pointwise bound `hx0`
          simpa [Real.norm_eq_abs, abs_of_nonneg hL, abs_of_nonneg hR, abs_mul, hCabs, hIabs] using hx0
        exact (MeasureTheory.memLp_two_iff_integrable_sq hF_meas).2 hF2_int
      -- Orthogonality of the coefficient functions `F krest` against the 1D eigenfunctions.
      have hF_orth :
          ∀ krest : Fin n → ℕ, ∀ k0 : ℕ,
            ∫ x0 : ℝ, (F krest x0) * eigenfunctionReal ξ k0 x0 = 0 := by
        intro krest k0
        -- combined index on `Fin (n+1)`
        let k : Fin (n + 1) → ℕ := Fin.cons k0 krest
        have hk : (∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x) = 0 :=
          horth k
        -- rewrite the integral on the product model using `e`
        have hk' :
            (∫ y : (ℝ × (Fin n → ℝ)),
                g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)) = 0 := by
          -- Change variables using the measure-preserving equivalence `e`.
          let φ : (ℝ × (Fin n → ℝ)) → ℝ :=
            fun y => g' y * eigenfunctionProd (n := n + 1) ξ k (e.symm y)
          -- rewrite the goal in terms of the auxiliary integrand `φ`
          change (∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ)))) = 0
          have hcomp :
              (∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ)))
                =
              ∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ))) :=
            (MeasurePreserving.integral_comp'
              (μ := (volume : Measure (Fin (n + 1) → ℝ)))
              (ν := (volume : Measure (ℝ × (Fin n → ℝ))))
              hmp (g := φ))
          have hφ :
              (∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ)))
                =
              ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x
                  ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
            refine MeasureTheory.integral_congr_ae ?_
            refine Filter.Eventually.of_forall ?_
            intro x
            dsimp [φ, g']
            -- rewrite `e.symm (e x)` to `x`
            simp
          calc
            (∫ y : (ℝ × (Fin n → ℝ)), φ y ∂(volume : Measure (ℝ × (Fin n → ℝ))))
                =
              ∫ x : (Fin (n + 1) → ℝ), φ (e x) ∂(volume : Measure (Fin (n + 1) → ℝ)) := by
                simpa using hcomp.symm
            _ =
              ∫ x : (Fin (n + 1) → ℝ), g x * eigenfunctionProd (n := n + 1) ξ k x
                  ∂(volume : Measure (Fin (n + 1) → ℝ)) := hφ
            _ = 0 := by simpa using hk
        -- simplify `eigenfunctionProd` under `e.symm`
        have hk'' :
            (∫ y : (ℝ × (Fin n → ℝ)),
                g' y *
                  (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)) = 0 := by
          -- split the `Fin (n+1)` product at `0` and use the description of `e.symm`.
          have hprod :
              (fun y : (ℝ × (Fin n → ℝ)) =>
                  eigenfunctionProd (n := n + 1) ξ k (e.symm y)) =
                fun y : (ℝ × (Fin n → ℝ)) =>
                  eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2 := by
            funext y
            simp [eigenfunctionProd, k, Fin.prod_univ_succ, e,
              MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ, Fin.cons_zero]
          -- rewrite the integrand in `hk'` using `hprod`
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
            -- use `hy` to rewrite the integrand
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
          -- conclude from `hk'`
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
        -- apply Fubini to identify this integral with the 1D orthogonality condition for `F krest`
        have h_int :
            Integrable
              (fun y : (ℝ × (Fin n → ℝ)) =>
                g' y * (eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2))
              (volume : Measure (ℝ × (Fin n → ℝ))) := by
          -- show both factors are `L²` and use Hölder with `p=q=2`
          have hH :
              MemLp (fun y : (ℝ × (Fin n → ℝ)) =>
                  eigenfunctionReal ξ k0 y.1 * eigenfunctionProd (n := n) ξ krest y.2)
                2 (volume : Measure (ℝ × (Fin n → ℝ))) := by
            -- use `p=2` characterization via integrability of the square
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
                  aestronglyMeasurable_eigenfunctionProd (n := n) (ξ := ξ) (hξ := hξ) krest
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
                  Integrable (fun x0 : ℝ => (eigenfunctionReal ξ k0 x0) ^ 2) (volume : Measure ℝ) := by
                simpa using
                  (HarmonicOscillator.integrable_eigenfunctionReal_sq (ξ := ξ) (hξ := hξ) (n := k0))
              have h2 :
                  Integrable (fun z : (Fin n → ℝ) => (eigenfunctionProd (n := n) ξ krest z) ^ 2)
                    (volume : Measure (Fin n → ℝ)) := by
                simpa using integrable_eigenfunctionProd_sq (n := n) (ξ := ξ) (hξ := hξ) krest
              simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, mul_pow] using
                (MeasureTheory.Integrable.mul_prod (μ := (volume : Measure ℝ))
                  (ν := (volume : Measure (Fin n → ℝ)))
                  (f := fun x0 : ℝ => (eigenfunctionReal ξ k0 x0) ^ 2)
                  (g := fun z : (Fin n → ℝ) => (eigenfunctionProd (n := n) ξ krest z) ^ 2)
                  h1 h2)
            exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hint
          exact MeasureTheory.MemLp.integrable_mul hg' hH
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
        -- pull out the scalar `eigenfunctionReal ξ k0 x0` from the inner integral
        have hfub' :
            (∫ x0 : ℝ,
              ∫ z : (Fin n → ℝ),
                g' (x0, z) * (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                ∂(volume : Measure (Fin n → ℝ))
              ∂(volume : Measure ℝ))
              =
            ∫ x0 : ℝ, (F krest x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards with x0
          -- pull out the scalar `eigenfunctionReal ξ k0 x0` from the inner integral
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
          -- rewrite `F` and finish
          dsimp [F]
          exact hinner
        -- conclude
        have : ∫ x0 : ℝ, (F krest x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ) = 0 := by
          -- rewrite `hk''` using `hfub` and `hfub'` (avoid `simp`-expanding eigenfunctions)
          have hk_fub :
              (∫ x0 : ℝ,
                    ∫ z : (Fin n → ℝ),
                      g' (x0, z) *
                        (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                        ∂(volume : Measure (Fin n → ℝ))
                    ∂(volume : Measure ℝ)) = 0 := by
            -- use `hfub` to rewrite the product integral in `hk''`
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
          -- now use `hfub'` to identify the iterated integral with the 1D coefficient integral
          calc
            (∫ x0 : ℝ, (F krest x0) * eigenfunctionReal ξ k0 x0 ∂(volume : Measure ℝ))
                =
              (∫ x0 : ℝ,
                    ∫ z : (Fin n → ℝ),
                      g' (x0, z) *
                        (eigenfunctionReal ξ k0 x0 * eigenfunctionProd (n := n) ξ krest z)
                        ∂(volume : Measure (Fin n → ℝ))
                    ∂(volume : Measure ℝ)) := by
                simpa using hfub'.symm
            _ = 0 := hk_fub
        simpa [mul_comm] using this
      -- Apply 1D completeness to each coefficient function `F krest`.
      have hF_zero :
          ∀ krest : Fin n → ℕ, (F krest) =ᵐ[(volume : Measure ℝ)] 0 := by
        intro krest
        refine HarmonicOscillator.ae_eq_zero_of_forall_integral_eigenfunctionReal_eq_zero
          (ξ := ξ) hξ (hg := hF_memLp krest) ?_
        intro k0
        simpa [mul_assoc] using hF_orth krest k0
      -- For a.e. `x0`, all coefficients in the remaining coordinates vanish.
      haveI : Countable (Fin n → ℕ) := by infer_instance
      have hF_zero_all :
          ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ), ∀ krest : Fin n → ℕ, F krest x0 = 0 := by
        refine (MeasureTheory.ae_all_iff).2 ?_
        intro krest
        exact hF_zero krest
      -- Slice `MemLp` for `x0 ↦ g' (x0, ·)`
      have hslice_memLp :
          ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
            MemLp (fun z : (Fin n → ℝ) => g' (x0, z)) 2 (volume : Measure (Fin n → ℝ)) := by
        have hgsq_int :
            Integrable (fun p : ℝ × (Fin n → ℝ) => (g' p) ^ 2)
              (volume : Measure (ℝ × (Fin n → ℝ))) :=
          MeasureTheory.MemLp.integrable_sq hg'
        have hslice_meas :
            ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
              AEStronglyMeasurable (fun z : (Fin n → ℝ) => g' (x0, z))
                (volume : Measure (Fin n → ℝ)) := by
          simpa using (hg'.1.prodMk_left (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ))))
        have hslice_sq_int :
            ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
              Integrable (fun z : (Fin n → ℝ) => (g' (x0, z)) ^ 2)
                (volume : Measure (Fin n → ℝ)) := by
          simpa using hgsq_int.prod_right_ae
        filter_upwards [hslice_meas, hslice_sq_int] with x0 hmeas hint
        exact (MeasureTheory.memLp_two_iff_integrable_sq hmeas).2 hint
      -- Apply the induction hypothesis in the remaining coordinates for a.e. `x0`.
      have hslice_zero :
          ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
            (fun z : (Fin n → ℝ) => g' (x0, z)) =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
        filter_upwards [hslice_memLp, hF_zero_all] with x0 hx0 hcoeff0
        have horth_slice :
            ∀ krest : Fin n → ℕ,
              ∫ z : (Fin n → ℝ), g' (x0, z) * eigenfunctionProd (n := n) ξ krest z = 0 := by
          intro krest
          simpa [F] using hcoeff0 krest
        exact ih (g := fun z : (Fin n → ℝ) => g' (x0, z)) hx0 horth_slice
      -- Conclude `g' = 0` a.e. by showing `∫ (g')^2 = 0`.
      have hgsq_int :
          Integrable (fun p : (ℝ × (Fin n → ℝ)) => (g' p) ^ 2)
            (volume : Measure (ℝ × (Fin n → ℝ))) :=
        MeasureTheory.MemLp.integrable_sq hg'
      have hinner_ae :
          ∀ᵐ x0 : ℝ ∂(volume : Measure ℝ),
            (∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))) = 0 := by
        filter_upwards [hslice_zero] with x0 hx0
        have : (fun z : (Fin n → ℝ) => (g' (x0, z)) ^ 2) =ᵐ[(volume : Measure (Fin n → ℝ))] 0 := by
          filter_upwards [hx0] with z hz
          simp [hz]
        simpa using (MeasureTheory.integral_eq_zero_of_ae (μ := (volume : Measure (Fin n → ℝ))) this)
      have hgsq_zero :
          (∫ p : (ℝ × (Fin n → ℝ)), (g' p) ^ 2 ∂(volume : Measure (ℝ × (Fin n → ℝ)))) = 0 := by
        have hfub :
            (∫ p : (ℝ × (Fin n → ℝ)), (g' p) ^ 2 ∂(volume : Measure (ℝ × (Fin n → ℝ))))
              =
            ∫ x0 : ℝ,
              ∫ z : (Fin n → ℝ), (g' (x0, z)) ^ 2 ∂(volume : Measure (Fin n → ℝ))
              ∂(volume : Measure ℝ) := by
          simpa using
            (MeasureTheory.integral_prod
              (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Fin n → ℝ)))
              (f := fun p : (ℝ × (Fin n → ℝ)) => (g' p) ^ 2) hgsq_int)
        rw [hfub]
        exact MeasureTheory.integral_eq_zero_of_ae (μ := (volume : Measure ℝ)) hinner_ae
      have hgsq_ae0 :
          (fun p : (ℝ × (Fin n → ℝ)) => (g' p) ^ 2)
            =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] 0 := by
        have hnonneg : 0 ≤ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] fun p => (g' p) ^ 2 :=
          Filter.Eventually.of_forall (fun _ => sq_nonneg _)
        exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hgsq_int).1 hgsq_zero
      have hg'_ae0 : g' =ᵐ[(volume : Measure (ℝ × (Fin n → ℝ)))] 0 := by
        filter_upwards [hgsq_ae0] with p hp
        have : (g' p) ^ 2 = 0 := by simpa using hp
        have : g' p = 0 := eq_zero_of_pow_eq_zero (n := 2) this
        simpa using this
      -- Transport back along the measure-preserving equivalence `e`.
      have hq : MeasureTheory.Measure.QuasiMeasurePreserving e
          (volume : Measure (Fin (n + 1) → ℝ)) (volume : Measure (ℝ × (Fin n → ℝ))) :=
        hmp.quasiMeasurePreserving
      have : g =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] 0 := by
        have hcomp :
            g' ∘ e =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))]
              (0 : (ℝ × (Fin n → ℝ)) → ℝ) ∘ e :=
          hq.ae_eq_comp hg'_ae0
        have hcomp0 : g' ∘ e =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] 0 := by
          simpa using hcomp
        have hge : g' ∘ e =ᵐ[(volume : Measure (Fin (n + 1) → ℝ))] g := by
          refine Filter.Eventually.of_forall ?_
          intro x
          dsimp [g']
          simp
        exact hge.symm.trans hcomp0
      exact this

end SpaceTimeHermite

end

end PhysLean
