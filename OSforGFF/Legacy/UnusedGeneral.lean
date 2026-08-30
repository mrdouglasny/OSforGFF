/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.General.FourierTransforms
import OSforGFF.Spacetime.Basic
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.General.HadamardExp
import OSforGFF.General.L2TimeIntegral
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order

/-!
# LEGACY — unused general-analysis lemmas (off the build graph)

**Status: legacy.** Proven general-analysis material from the original development that no
declaration on the build graph consumes. Preserved here with full proofs; **not on the root
import graph**. Verify in isolation with

    lake env lean OSforGFF/Legacy/UnusedGeneral.lean

Former `private` markers are dropped for archival visibility. Declarations keep their original
namespaces; each block re-declares the `open`/`variable` context of its source file.

## Supersession map

From `General/FourierTransforms.lean` (never wired into the reflection-positivity chain — the
OS3 proof runs through `fourier_lorentzian_1d`/`fourier_exponential_decay'` and the mixed
representation instead):
- `exp_pos_integrableOn_Iio`, `exp_pos_integrableOn_Iic` — growth-side integrability twins of
  the used decay lemmas.
- `fourier_exponential_decay` — negative-frequency variant of the used
  `fourier_exponential_decay'`.
- `exp_factorization_reflection` — pointwise exponential factorization; the factorization
  enters the library through the mixed representation (`OS/OS3_MixedRepInfra.lean`) instead.
- `tripleReorder`, `measurePreserving_tripleReorder` (both formerly `private`; moved
  2026-08-30) — a measure-preserving reordering `(x,(y,k)) ↦ (k,(x,y))` of a triple
  product; the Fubini swaps on the graph use `fubini_s_ksp_swap`/`fubini_ksp_xy_swap`
  (`OS/OS3_MixedRepInfra.lean`) instead.

From `General/FunctionalAnalysis.lean`:
- `schwartzToL2'` — type-representation variant of the used `schwartzToL2`.
- `linfty_mul_L2_CLM_norm_bound` — norm bound for the used `linfty_mul_L2_CLM`; consumers only
  need the operator and its pointwise spec.
- `locallyIntegrable_of_rpow_decay_real` — superseded by the `weightedIntegrable`-based route
  to OS1 local integrability.
- `SchwartzMap.integrable_mul_bounded`, `SchwartzMap.integrable_conj` (the former
  `section SchwartzBounded`) — Fourier-type integrability helpers; the generic library uses
  mathlib's Schwartz integrability API directly.
- `norm_exp_I_mul_real` — the `neg` twin is live; this sign is not.
- `Complex.ofRealCLM_continuous_compLp`, `composed_function`, `embedding_real_to_complex`,
  `liftMeasure_real_to_complex` (moved 2026-08-30) — the real→complex Lp measure-lifting
  chain; the construction works on `WeakDual` field configurations via Minlos, never
  through an Lp lift.

From `Covariance/RealForm.lean`:
- `QFT.momentumWeightMeasure` (moved 2026-08-30) — the weighted momentum-space measure
  with density `(‖k‖² + m²)⁻¹`; the covariance embedding works with explicit weighted
  integrands rather than a weighted measure.

From `General/HadamardExp.lean`:
- `entrywiseExpSeriesTerm` — packaged series term; the entrywise-exponential development uses
  `entrywiseExp_hadamardSeries` (entrywise `tsum`) directly.

The ENTIRE former `General/FrobeniusPositivity.lean` (the file is deleted from the build
graph; its one headline had no consumers and its five helpers no consumers outside the file):
- `frobenius_eq_trace_transpose_mul`, `congr_transpose_mul_mul_ne_zero`,
  `psd_cauchy_schwarz`, `psd_offdiag_zero_of_diag_zero`,
  `posSemidef_diag_pos_exists_of_ne_zero` — the supporting chain, and
- `frobenius_pos_of_psd_posdef` — strict Frobenius positivity `0 < ⟪G, B⟫` for `G` PSD
  nonzero and `B` PD; the reflection-positivity argument only needs the semidefinite
  versions (`General/FrobeniusPositivity` in name only — the on-graph PSD machinery lives in
  `General/HadamardExp.lean` and `OS/OS3_ReflectionPositivity.lean`).

From `General/L2TimeIntegral.lean` (the time-averaging program superseded by the OS4
clustering route through `schwingerTwoPointFunction`; the live chain runs through
`time_average_memLp_two`):
- `integral_swap_Icc`, `setIntegral_L2_bound` — helpers consumed only by
  `L2_time_average_bound` (moved with it).
- `L2_time_average_bound` — L² bound for time averages.
- the former `section Minkowski`: `cauchy_schwarz_integral`,
  `integrable_mul_of_sq_integrable`, `sqrt_integral_sq_add_le`, `sqrt_integral_sq_mul`,
  `memLp_two_weighted`, `memLp_two_weighted_sum`, `integrable_sq_of_memLp_two` (all formerly
  `private`) and their sole consumer `minkowski_weighted_L2_sum_proved`.
-/

universe u

/-! ### From `General/FourierTransforms.lean` -/

section FourierTransforms

open MeasureTheory Complex Real
open scoped BigOperators FourierTransform

noncomputable section

/-- Exponential e^{bx} is integrable on (-∞, a) when b > 0.
    Proved by change of variables from exp_neg_integrableOn_Ioi. -/
theorem exp_pos_integrableOn_Iio (a : ℝ) {b : ℝ} (h : 0 < b) :
    MeasureTheory.IntegrableOn (fun x => Real.exp (b * x)) (Set.Iio a) MeasureTheory.volume := by
  have h_neg : MeasureTheory.IntegrableOn (fun x => Real.exp (-b * x)) (Set.Ioi (-a)) MeasureTheory.volume :=
    exp_neg_integrableOn_Ioi (-a) h
  have h_eq : (fun x => Real.exp (b * x)) = (fun x => Real.exp (-b * (-x))) := by
    ext x; ring_nf
  rw [h_eq]
  have h_set : Set.Iio a = -Set.Ioi (-a) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_neg, Set.mem_Ioi]
    constructor <;> intro hx <;> linarith
  rw [h_set]
  exact h_neg.comp_neg

/-- Exponential e^{bx} is integrable on (-∞, a] when b > 0.
    Follows from Iio version since measure of a point is 0. -/
theorem exp_pos_integrableOn_Iic (a : ℝ) {b : ℝ} (h : 0 < b) :
    MeasureTheory.IntegrableOn (fun x => Real.exp (b * x)) (Set.Iic a) MeasureTheory.volume :=
  integrableOn_exp_mul_Iic h a

/-- Variant with negative frequency convention e^{-ikx}. -/
lemma fourier_exponential_decay (μ : ℝ) (hμ : 0 < μ) (k : ℝ) :
    ∫ x : ℝ, Complex.exp (-Complex.I * k * x) * Real.exp (-μ * |x|) =
      2 * μ / (k^2 + μ^2) := by
  -- e^{-ikx} = e^{i(-k)x}
  have h1 : ∫ x : ℝ, Complex.exp (-Complex.I * k * x) * Real.exp (-μ * |x|) =
      ∫ x : ℝ, Complex.exp (Complex.I * (-k) * x) * Real.exp (-μ * |x|) := by
    congr 1; funext x; ring_nf
  rw [h1]
  convert fourier_exponential_decay' μ hμ (-k) using 2 <;> simp

/-- The exponential from the Lorentzian Fourier transform factorizes.
    For x, y with x ≥ 0 and y ≤ 0, we have |x - y| = x - y = x + |y|,
    so e^{-μ|x-y|} = e^{-μx} · e^{-μ|y|} = e^{-μx} · e^{μy}. -/
lemma exp_factorization_reflection (μ : ℝ) (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0) :
    Real.exp (-μ * |x - y|) = Real.exp (-μ * x) * Real.exp (μ * y) := by
  have h_diff : |x - y| = x - y := abs_of_nonneg (by linarith)
  rw [h_diff]
  rw [← Real.exp_add]
  congr 1
  ring


end

end FourierTransforms

/-! ### From `General/FunctionalAnalysis.lean` -/

section FunctionalAnalysis

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open scoped FourierTransform SchwartzMap

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- Alternative embedding that produces the exact L² type expected by the unprimed theorems.
    This maps Schwartz functions to Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))).
    The difference from schwartzToL2 is only in the type representation, not the mathematical content. -/
noncomputable def schwartzToL2' (d : ℕ) [NeZero d] [Fintype (Fin d)] :
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ →L[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))

/-- The operator norm of the multiplication operator is bounded by C.
    This gives ‖Mg f‖₂ ≤ C · ‖f‖₂ for all f ∈ L². -/
theorem linfty_mul_L2_CLM_norm_bound {μ : Measure α}
    (g : α → ℂ) (hg_meas : Measurable g) (C : ℝ) (hC : 0 ≤ C)
    (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ C)
    (f : Lp ℂ 2 μ) :
    ‖linfty_mul_L2_CLM g hg_meas C hg_bound f‖ ≤ C * ‖f‖ := by
  have hg_mem := memLp_top_of_bound hg_meas.aestronglyMeasurable C hg_bound
  calc
    _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ)‖ * ‖hg_mem.toLp‖ * ‖f‖ := by
      apply ContinuousLinearMap.norm_holder_apply_apply_le
    _ ≤ C * ‖f‖ := by
      simp only [ContinuousLinearMap.opNorm_mul, Lp.norm_toLp, eLpNorm_exponent_top, one_mul]
      gcongr
      refine toReal_le_of_le_ofReal hC ?_
      exact eLpNormEssSup_le_of_ae_bound hg_bound

/-- Functions with polynomial decay are locally integrable.
    For d-dimensional space, if α < d and |f(x)| ≤ C‖x‖^{-α}, then f is locally integrable. -/
theorem locallyIntegrable_of_rpow_decay_real {d : ℕ} (hd : d ≥ 3)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {C : ℝ} {α : ℝ}
    (hC : C > 0) (hα : α < d)
    (h_decay : ∀ x, |f x| ≤ C * ‖x‖ ^ (-α))
    (h_meas : AEStronglyMeasurable f volume) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  -- Cover K with ball 0 1 and K \ ball 0 (1/2)
  have h_cover : K ⊆ (K ∩ Metric.ball 0 1) ∪ (K \ Metric.ball 0 (1/2)) := by
    intro x hx
    by_cases hxb : x ∈ Metric.ball 0 1
    · exact Or.inl ⟨hx, hxb⟩
    · simp only [Metric.mem_ball, dist_zero_right, not_lt] at hxb
      right
      constructor
      · exact hx
      · simp only [Metric.mem_ball, dist_zero_right, not_lt]
        linarith
  apply IntegrableOn.mono_set _ h_cover
  apply IntegrableOn.union
  · -- IntegrableOn f (K ∩ ball 0 1)
    apply IntegrableOn.mono_set _ Set.inter_subset_right
    exact integrableOn_ball_of_rpow_decay (by omega : d ≥ 1) hC hα (by norm_num : (0:ℝ) < 1)
      h_decay h_meas
  · -- IntegrableOn f (K \ ball 0 (1/2))
    exact integrableOn_compact_diff_ball hK hC (by norm_num : (0:ℝ) < 1/2) h_decay h_meas

section SchwartzBounded

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {μ : Measure E} [μ.HasTemperateGrowth]

/-- A Schwartz function times a bounded measurable function is integrable.
    This is the key technical lemma for Fourier-type integrals. -/
lemma SchwartzMap.integrable_mul_bounded (f : SchwartzMap E ℂ) (g : E → ℂ)
    (hg_meas : Measurable g) (hg_bdd : ∀ x, ‖g x‖ ≤ 1) :
    Integrable (fun x => f x * g x) μ := by
  have hf_int : Integrable f μ := f.integrable
  -- Use bdd_mul: Integrable f → AEStronglyMeasurable g → (∀ᵐ x, ‖g x‖ ≤ C) → Integrable (g * f)
  -- Then convert by commutativity
  have hg_ae : AEStronglyMeasurable g μ := hg_meas.aestronglyMeasurable
  have hg_ae_bdd : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := Filter.Eventually.of_forall hg_bdd
  exact Integrable.mul_bdd hf_int hg_ae hg_ae_bdd

/-- The conjugate of a Schwartz function is integrable. -/
lemma SchwartzMap.integrable_conj (f : SchwartzMap E ℂ) :
    Integrable (fun y => starRingEnd ℂ (f y)) μ := by
  have hf_int : Integrable f μ := f.integrable
  have hf_star_meas : AEStronglyMeasurable (fun y => starRingEnd ℂ (f y)) μ :=
    hf_int.aestronglyMeasurable.star
  have h_norm_eq : ∀ᵐ y ∂μ, ‖f y‖ = ‖starRingEnd ℂ (f y)‖ := by
    filter_upwards with y
    exact (RCLike.norm_conj (f y)).symm
  exact hf_int.congr' hf_star_meas h_norm_eq

end SchwartzBounded

/-- Complex exponential of pure imaginary argument has norm 1. -/
lemma norm_exp_I_mul_real (r : ℝ) : ‖Complex.exp (Complex.I * r)‖ = 1 :=
  norm_exp_I_mul_ofReal r

end

end FunctionalAnalysis

/-! ### From `General/HadamardExp.lean` -/

section HadamardExp

open Complex Filter
open scoped BigOperators Topology

namespace OSforGFF

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- One term of the Hadamard-series for the entrywise exponential. -/
noncomputable def entrywiseExpSeriesTerm (R : Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  (1 / (Nat.factorial n : ℝ)) • hadamardPow R n

end OSforGFF

end HadamardExp

/-! ### The entire former `General/FrobeniusPositivity.lean` -/

section FrobeniusPositivity

open Matrix
open scoped BigOperators MatrixOrder

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Helper: Frobenius inner product equals `trace (Gᵀ * B)` (real case). -/
lemma frobenius_eq_trace_transpose_mul
  (G B : Matrix ι ι ℝ) :
  (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) := by
  classical
  -- Expand the trace of Gᵀ * B
  have htrace : Matrix.trace (G.transpose * B) = ∑ i, ∑ k, G k i * B k i := by
    simp [Matrix.trace, Matrix.mul_apply]
  -- Reorder the Frobenius double sum and rename indices to match htrace
  calc
    (∑ j, ∑ l, G j l * B j l) = ∑ i, ∑ k, G k i * B k i := by
          simpa using
            (Finset.sum_comm :
              (∑ j, ∑ l, G j l * B j l) = (∑ i, ∑ k, G k i * B k i))
    _ = Matrix.trace (G.transpose * B) := htrace.symm

/-- Congruence by an orthogonal/invertible matrix preserves nonzeroness (real case).
If `U * Uᵀ = 1`, then `Uᵀ G U ≠ 0` whenever `G ≠ 0`. -/
lemma congr_transpose_mul_mul_ne_zero
  (U G : Matrix ι ι ℝ) (hU_right : U * U.transpose = 1) (hG_ne_zero : G ≠ 0) :
  U.transpose * G * U ≠ 0 := by
  intro hH
  -- Conjugate back with U on the left and Uᵀ on the right to recover G
  have hcalc : U * (U.transpose * G * U) * U.transpose
      = (U * U.transpose) * G * (U * U.transpose) := by
    simp [Matrix.mul_assoc]
  have hG_eq : G = U * (U.transpose * G * U) * U.transpose := by
    simpa [hU_right, Matrix.one_mul, Matrix.mul_one] using hcalc.symm
  have : G = 0 := by simpa [hH, Matrix.mul_zero, Matrix.zero_mul] using hG_eq
  exact hG_ne_zero this

/-- Cauchy–Schwarz for the semi-inner product induced by a PSD real matrix.
For all vectors x,y: (xᵀ H y)^2 ≤ (xᵀ H x) (yᵀ H y). -/
lemma psd_cauchy_schwarz
  (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) (x y : ι → ℝ) :
  ((x ⬝ᵥ H.mulVec y)^2) ≤ (x ⬝ᵥ H.mulVec x) * (y ⬝ᵥ H.mulVec y) := by
  classical
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH_psd.nonneg
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at hB
  subst hB
  have hform (a b : ι → ℝ) :
      a ⬝ᵥ (B.transpose * B).mulVec b = (B.mulVec a) ⬝ᵥ (B.mulVec b) := by
    have h1 : (B.transpose * B).mulVec b = B.transpose.mulVec (B.mulVec b) := by
      exact (Matrix.mulVec_mulVec b B.transpose B).symm
    calc
      a ⬝ᵥ (B.transpose * B).mulVec b
          = a ⬝ᵥ B.transpose.mulVec (B.mulVec b) := by rw [h1]
      _ = (Matrix.vecMul a B.transpose) ⬝ᵥ (B.mulVec b) := by
        exact dotProduct_mulVec a Bᵀ (B.mulVec b)
      _ = (B.mulVec a) ⬝ᵥ (B.mulVec b) := by
        have := (Matrix.vecMul_transpose (A := B) (x := a))
        simpa using congrArg (fun w => w ⬝ᵥ (B.mulVec b)) this
  let u : ι → ℝ := B.mulVec x
  let v : ι → ℝ := B.mulVec y
  -- xᵀ (Bᵀ B) y = (Bx)⋅(By), and similarly for x/x and y/y
  have hxy : x ⬝ᵥ (B.transpose * B).mulVec y = u ⬝ᵥ v := by
    simpa [u, v] using hform x y
  have hxx : x ⬝ᵥ (B.transpose * B).mulVec x = u ⬝ᵥ u := by
    simpa [u] using hform x x
  have hyy : y ⬝ᵥ (B.transpose * B).mulVec y = v ⬝ᵥ v := by
    simpa [v] using hform y y
  -- Cauchy–Schwarz in ℝ^ι: |u⋅v|^2 ≤ (u⋅u)(v⋅v)
  have hCS : (u ⬝ᵥ v)^2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    classical
    -- Finset version of Cauchy–Schwarz with s = univ
    simpa [dotProduct, sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
        (f := fun i => u i) (g := fun i => v i))
  simpa [hxy, hxx, hyy] using hCS

/-- If H is PSD over ℝ and H ii = H jj = 0 then H ij = 0. -/
lemma psd_offdiag_zero_of_diag_zero
  (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) {i j : ι}
  (hii : H i i = 0) (hjj : H j j = 0) : H i j = 0 := by
  classical
  -- Apply Cauchy–Schwarz with x = e_i, y = e_j
  have hcs := psd_cauchy_schwarz H hH_psd (Pi.single i (1:ℝ)) (Pi.single j (1:ℝ))
  -- Rewrite each quadratic form
  have hx : (Pi.single i (1:ℝ)) ⬝ᵥ H.mulVec (Pi.single i 1) = H i i := by simp
  have hy : (Pi.single j (1:ℝ)) ⬝ᵥ H.mulVec (Pi.single j 1) = H j j := by simp
  have hxy : (Pi.single i (1:ℝ)) ⬝ᵥ H.mulVec (Pi.single j 1) = H i j := by simp
  -- Substitute and use hii, hjj
  have : (H i j)^2 ≤ (H i i) * (H j j) := by simpa [hx, hy, hxy]
    using hcs
  -- Right side is 0, left is square ≥ 0, hence equality and H i j = 0 over ℝ
  have : (H i j)^2 ≤ 0 := by simpa [hii, hjj]
  have hsq_nonneg : 0 ≤ (H i j)^2 := by have := sq_nonneg (H i j); simpa using this
  have : (H i j)^2 = 0 := le_antisymm this hsq_nonneg
  exact sq_eq_zero_iff.mp this

/-- For a real PSD matrix, if it is nonzero then some diagonal entry is strictly positive. -/
lemma posSemidef_diag_pos_exists_of_ne_zero
  (H : Matrix ι ι ℝ) (hH_psd : H.PosSemidef) (hH_ne_zero : H ≠ 0) :
  ∃ i, 0 < H i i := by
  classical
  -- Suppose all diagonal entries are ≤ 0; PSD gives ≥ 0, hence all zeros
  by_contra h
  push Not at h
  have hdiag_nonneg : ∀ i, 0 ≤ H i i := fun i => hH_psd.diag_nonneg
  have hdiag_zero : ∀ i, H i i = 0 := fun i => le_antisymm (h i) (hdiag_nonneg i)
  -- Show all off-diagonals are zero
  have hoff : ∀ i j, H i j = 0 := by
    intro i j
    exact psd_offdiag_zero_of_diag_zero H hH_psd (hdiag_zero i) (hdiag_zero j)
  -- Hence H = 0, contradiction
  have : H = 0 := by
    ext i j
    simp [hoff i j]
  exact hH_ne_zero this

/-- Frobenius positivity for a nonzero PSD matrix against a PD matrix (real case).
If `G` is positive semidefinite and nonzero, and `B` is positive definite,
then the Frobenius inner product `∑ j, ∑ l, G j l * B j l` is strictly positive.

High-level proof sketch (to be formalized):
- Use spectral theorem for real symmetric PD matrices: B = U D Uᵀ with D diagonal, diag(λ), λ > 0.
- Let H := Uᵀ G U. Then H is PSD and H ≠ 0 (congruence by invertible U).
- Frobenius inner product equals trace: ⟪G,B⟫ = tr(G B) = tr(H D) = ∑ i λ i * H i i.
- For PSD H, diagonal entries are ≥ 0, and H ≠ 0 ⇒ ∃ i, H i i > 0.
- Since all λ i > 0, the sum is strictly positive.
- This avoids Cholesky and uses spectral decomposition/unitary congruence invariance.
-/
lemma frobenius_pos_of_psd_posdef
  (G B : Matrix ι ι ℝ) (hG_psd : G.PosSemidef) (hG_ne_zero : G ≠ 0) (hB : B.PosDef) :
  0 < ∑ j, ∑ l, G j l * B j l := by
  classical
  -- Step 1: rewrite as a trace
  have hfrob_trace : (∑ j, ∑ l, G j l * B j l) = Matrix.trace (G.transpose * B) :=
    frobenius_eq_trace_transpose_mul G B
  -- Step 2: spectral decomposition of B using positive definite eigenvalues
  have hB_herm : B.IsHermitian := hB.1
  have hd_pos : ∀ i, 0 < hB_herm.eigenvalues i := hB.eigenvalues_pos
  -- Get the spectral decomposition B = U * D * U*
  have hB_spectral := hB_herm.spectral_theorem
  -- Define the eigenvector unitary and its underlying matrix, and eigenvalue function
  let Uu := hB_herm.eigenvectorUnitary
  let U : Matrix ι ι ℝ := (Uu : Matrix ι ι ℝ)
  let d : ι → ℝ := hB_herm.eigenvalues
  -- Since we're over ℝ, star = transpose and RCLike.ofReal = identity
  have hB_decomp : B = U * Matrix.diagonal d * U.transpose := by
    rw [hB_spectral]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
               Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id, id]
    rfl
  -- Define H := Uᵀ * G * U and show PSD
  let H : Matrix ι ι ℝ := U.transpose * G * U
  have hH_psd : H.PosSemidef := by
    rw [show H = U.conjTranspose * G * U from by
        simp [H, Matrix.conjTranspose_eq_transpose_of_trivial]]
    exact hG_psd.conjTranspose_mul_mul_same U
  -- Use a local lemma to avoid inline unitary algebra: H ≠ 0
  have hH_ne_zero : H ≠ 0 := by
    -- From the unitary eigenvector matrix, we have U * Uᵀ = 1 (over ℝ)
    have hU_mem : U ∈ Matrix.unitaryGroup ι ℝ := by
      -- Uu is a unitary group element, coerce to show membership
      rw [show U = Uu.val from rfl]
      exact Uu.property

    have hU_unitary : U * U.conjTranspose = 1 := by
      exact Matrix.mem_unitaryGroup_iff.mp hU_mem

    have hU_right : U * U.transpose = 1 := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hU_unitary

    exact congr_transpose_mul_mul_ne_zero U G hU_right hG_ne_zero
  -- Trace cyclicity: reduce to trace(H * diagonal d)
  have hG_herm : G.IsHermitian := hG_psd.1
  have htrace_cycle : Matrix.trace (G.transpose * B) = Matrix.trace (H * (Matrix.diagonal d)) := by
    have hG_symm : G.transpose = G := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hG_herm
    rw [hG_symm, hB_decomp]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    simp [H, Matrix.mul_assoc]
  -- Expand trace(H * diagonal d) as ∑ i d i * H i i
  have htrace_sum : Matrix.trace (H * Matrix.diagonal d) = ∑ i, d i * H i i := by
    classical
    simp [Matrix.trace, Matrix.mul_apply, Matrix.diagonal, mul_comm]
  -- Diagonal entries of H are ≥ 0 from PSD
  have hdiag_nonneg : ∀ i, 0 ≤ H i i := fun i => hH_psd.diag_nonneg
  -- From nonzero PSD, some diagonal is positive (local lemma)
  have hdiag_pos_exists : ∃ i, 0 < H i i :=
    posSemidef_diag_pos_exists_of_ne_zero H hH_psd hH_ne_zero
  -- Conclude positivity: all d i > 0, some H i i > 0, and others ≥ 0
  rcases hdiag_pos_exists with ⟨i0, hi0pos⟩
  have hsum_pos : 0 < ∑ i, d i * H i i := by
    have h_pos : 0 < d i0 * H i0 i0 := mul_pos (hd_pos i0) hi0pos
    rw [← Finset.add_sum_erase Finset.univ (fun i => d i * H i i) (Finset.mem_univ i0)]
    have h_nonneg : 0 ≤ ∑ x ∈ Finset.univ.erase i0, d x * H x x := by
      apply Finset.sum_nonneg; intro i _
      exact mul_nonneg (le_of_lt (hd_pos i)) (hdiag_nonneg i)
    exact add_pos_of_pos_of_nonneg h_pos h_nonneg
  -- Transport back to the original Frobenius sum
  have htrace_pos : 0 < Matrix.trace (H * Matrix.diagonal d) := by
    simpa [htrace_sum] using hsum_pos
  have htrace_pos' : 0 < Matrix.trace (G.transpose * B) := by
    simpa [htrace_cycle] using htrace_pos
  simpa [hfrob_trace] using htrace_pos'

end FrobeniusPositivity

/-! ### From `General/L2TimeIntegral.lean` -/

section L2TimeIntegral

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace OSforGFF

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Main Theorem: L² Time Average Bound

We now prove the main theorem by integrating the pointwise bound over Ω
and swapping the order of integration via Fubini.
-/

/-- Helper: Fubini swap for ℝ × Ω with restricted measure. -/
lemma integral_swap_Icc (μ : Measure Ω) [SFinite μ]
    (f : ℝ × Ω → ℝ) (T : ℝ)
    (hf : Integrable f ((volume.restrict (Icc 0 T)).prod μ)) :
    (∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, f (s, ω)) ∂μ) =
    (∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), f (s, ω) ∂μ)) := by
  have h1 : ∫ (p : ℝ × Ω), f p ∂((volume.restrict (Icc 0 T)).prod μ) =
      ∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), f (s, ω) ∂μ) := integral_prod f hf
  have h2 : ∫ (p : ℝ × Ω), f p ∂((volume.restrict (Icc 0 T)).prod μ) =
      ∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, f (s, ω)) ∂μ := integral_prod_symm f hf
  rw [← h1, h2]

/-- Helper: setIntegral bound using uniform L² bound. -/
lemma setIntegral_L2_bound (μ : Measure Ω) [SFinite μ] (M_sq T : ℝ) (hT : T > 0)
    (A : ℝ → Ω → ℂ)
    (h_L2_bound : ∀ s, s ∈ Icc 0 T → ∫ ω, ‖A s ω‖^2 ∂μ ≤ M_sq)
    (h_int : IntegrableOn (fun s => ∫ ω, ‖A s ω‖^2 ∂μ) (Icc 0 T) volume) :
    (∫ (s : ℝ) in Icc 0 T, (∫ ω, ‖A s ω‖^2 ∂μ)) ≤ T * M_sq := by
  have h_vol : (volume : Measure ℝ) (Icc 0 T) ≠ ⊤ := by
    simp [Real.volume_Icc, ENNReal.ofReal_ne_top]
  calc (∫ (s : ℝ) in Icc 0 T, (∫ ω, ‖A s ω‖^2 ∂μ))
    ≤ ∫ (s : ℝ) in Icc 0 T, M_sq := by
        apply setIntegral_mono_on h_int (integrableOn_const h_vol) measurableSet_Icc
        intro s hs; exact h_L2_bound s hs
    _ = T * M_sq := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc]
        simp [ENNReal.toReal_ofReal (le_of_lt hT), smul_eq_mul]

/-- **L² bound for time averages.**

For A : ℝ → Ω → ℂ with uniform L² bound ∫_Ω ‖A_s‖² dμ ≤ M_sq for all s ∈ [0,T],
the time average satisfies:
$$\int_\Omega \left\|\frac{1}{T}\int_0^T A_s(\omega)\,ds\right\|^2 d\mu(\omega) \leq M_{sq}$$

**Proof outline:**
1. Cauchy-Schwarz pointwise: ‖(1/T)∫ A_s(ω) ds‖² ≤ (1/T) ∫ ‖A_s(ω)‖² ds
2. Integrate over Ω: ∫_Ω LHS dμ ≤ (1/T) ∫_Ω ∫_[0,T] ‖A_s‖² ds dμ
3. Fubini: = (1/T) ∫_[0,T] (∫_Ω ‖A_s‖² dμ) ds
4. Uniform bound: ≤ (1/T) ∫_[0,T] M_sq ds = (1/T) · T · M_sq = M_sq
-/
theorem L2_time_average_bound (μ : Measure Ω) [SFinite μ]
    (A : ℝ → Ω → ℂ) (M_sq : ℝ) (T : ℝ) (hT : T > 0)
    -- Uniform L² bound
    (h_L2_bound : ∀ s, s ∈ Icc 0 T → ∫ ω, ‖A s ω‖^2 ∂μ ≤ M_sq)
    -- Joint measurability for Fubini
    (h_joint_meas : AEStronglyMeasurable (Function.uncurry A)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Integrability of ‖A‖² on product (needed for Fubini)
    (h_prod_int : Integrable (fun p : ℝ × Ω => ‖A p.1 p.2‖^2)
        ((volume.restrict (Icc 0 T)).prod μ))
    -- Integrability of slice integrals (for Fubini step)
    (h_slice_int : IntegrableOn (fun s => ∫ ω, ‖A s ω‖^2 ∂μ) (Icc 0 T) volume)
    -- Measurability of time average (technical hypothesis)
    (h_avg_meas : AEStronglyMeasurable
        (fun ω => (1/T : ℂ) * ∫ s in Icc 0 T, A s ω) μ) :
    ∫ ω, ‖(1/T : ℂ) * ∫ s in Icc (0 : ℝ) T, A s ω‖^2 ∂μ ≤ M_sq := by
  /-
  The proof uses:
  1. scaled_time_average_pointwise_bound: pointwise Cauchy-Schwarz
  2. integral_mono_ae: integrate the a.e. pointwise inequality
  3. integral_const_mul: factor out (1/T)
  4. integral_swap_Icc: Fubini swap
  5. setIntegral_L2_bound: apply uniform bound
  -/
  -- Setup integrability for integral_mono
  have h_rhs_int : Integrable (fun ω => (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) μ := by
    have h_margin := h_prod_int.integral_prod_right
    exact h_margin.const_mul (1/T)

  -- From product integrability, get a.e. slice integrability
  have h_sq_meas : AEStronglyMeasurable (fun p : ℝ × Ω => ‖A p.1 p.2‖^2)
      ((volume.restrict (Icc 0 T)).prod μ) := h_joint_meas.norm.pow 2
  have h_ae_slice_int : ∀ᵐ (ω : Ω) ∂μ, IntegrableOn (fun s => ‖A s ω‖^2) (Icc 0 T) volume := by
    -- Use Integrable.swap to get integrability on the swapped product space
    have h_swap : Integrable ((fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap)
        (μ.prod (volume.restrict (Icc 0 T))) := h_prod_int.swap
    -- The swapped function is (ω, s) ↦ ‖A s ω‖²
    have h_eq : (fun p : ℝ × Ω => ‖A p.1 p.2‖^2) ∘ Prod.swap = fun p : Ω × ℝ => ‖A p.2 p.1‖^2 := rfl
    rw [h_eq] at h_swap
    -- Now apply integrable_prod_iff to get a.e. slice integrability
    -- Note: prod_swap takes AEStronglyMeasurable f (ν.prod μ) to (f ∘ swap) on (μ.prod ν)
    have h_meas_swap : AEStronglyMeasurable (fun p : Ω × ℝ => ‖A p.2 p.1‖^2)
        (μ.prod (volume.restrict (Icc 0 T))) := h_sq_meas.prod_swap
    exact ((integrable_prod_iff h_meas_swap).mp h_swap).1

  have h_lhs_int : Integrable (fun ω => ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2) μ := by
    have h_meas_sq := h_avg_meas.norm.pow 2
    apply h_rhs_int.mono h_meas_sq
    -- Use a.e. slice integrability to get the pointwise bound a.e.
    filter_upwards [h_ae_slice_int] with ω hω_int
    have h_lhs_nonneg : 0 ≤ ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s ω‖^2 := sq_nonneg _
    have h_rhs_nonneg : 0 ≤ (1/T : ℝ) * ∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2 := by
      apply mul_nonneg (by positivity); apply integral_nonneg; intro; positivity
    -- Simplify the power of functions applied to ω
    show ‖((fun x => ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc 0 T, A s x‖) ^ 2) ω‖ ≤ _
    simp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg h_lhs_nonneg, Real.norm_of_nonneg h_rhs_nonneg]
    exact scaled_time_average_pointwise_bound A T hT ω hω_int

  -- Main calculation
  calc ∫ (ω : Ω), ‖(1/T : ℂ) * ∫ (s : ℝ) in Icc (0 : ℝ) T, A s ω‖^2 ∂μ
    -- Step 1-2: Apply pointwise bound and integrate (use a.e. version)
    ≤ ∫ (ω : Ω), (1/T) * (∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) ∂μ := by
        apply integral_mono_ae h_lhs_int h_rhs_int
        -- Use a.e. slice integrability to get the bound a.e.
        filter_upwards [h_ae_slice_int] with ω hω_int
        exact scaled_time_average_pointwise_bound A T hT ω hω_int
    -- Step 3: Factor out (1/T)
    _ = (1/T) * (∫ (ω : Ω), (∫ (s : ℝ) in Icc 0 T, ‖A s ω‖^2) ∂μ) := by
        rw [integral_const_mul]
    -- Step 4: Fubini swap
    _ = (1/T) * (∫ (s : ℝ) in Icc 0 T, (∫ (ω : Ω), ‖A s ω‖^2 ∂μ)) := by
        rw [integral_swap_Icc μ (fun p => ‖A p.1 p.2‖^2) T h_prod_int]
    -- Step 5: Apply uniform bound
    _ ≤ (1/T) * (T * M_sq) := by
        apply mul_le_mul_of_nonneg_left
        · exact setIntegral_L2_bound μ M_sq T hT A h_L2_bound h_slice_int
        · positivity
    -- Step 6: Simplify
    _ = M_sq := by field_simp

/-! ## Minkowski Inequality for Weighted L² Sums

The triangle inequality in L²: √(∫(∑ wⱼfⱼ)²) ≤ ∑ wⱼ√(∫ fⱼ²)
for nonneg weights and functions. Proved by induction using Cauchy-Schwarz. -/

section Minkowski

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma cauchy_schwarz_integral
    {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_int : Integrable (fun x => (f x)^2) μ)
    (hg_int : Integrable (fun x => (g x)^2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) * Real.sqrt (∫ x, (g x)^2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from ⟨by norm_num, by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall hf_nn) (Filter.Eventually.of_forall hg_nn)
    (show MemLp f (ENNReal.ofReal 2) μ from by
      rw [show ENNReal.ofReal 2 = 2 from by norm_num, memLp_two_iff_integrable_sq_norm hf_meas]
      exact hf_int.congr (by filter_upwards with x; simp [Real.norm_eq_abs, sq_abs]))
    (show MemLp g (ENNReal.ofReal 2) μ from by
      rw [show ENNReal.ofReal 2 = 2 from by norm_num, memLp_two_iff_integrable_sq_norm hg_meas]
      exact hg_int.congr (by filter_upwards with x; simp [Real.norm_eq_abs, sq_abs]))
  have conv : ∀ (φ : α → ℝ), (fun a => φ a ^ (2:ℝ)) = fun a => (φ a)^(2:ℕ) := by
    intro φ; ext a; exact_mod_cast Real.rpow_natCast (φ a) 2
  simp only [conv, Real.sqrt_eq_rpow] at h ⊢; exact h

lemma integrable_mul_of_sq_integrable
    {f g : α → ℝ}
    (hf_int : Integrable (fun x => (f x)^2) μ)
    (hg_int : Integrable (fun x => (g x)^2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    Integrable (fun x => f x * g x) μ := by
  apply Integrable.mono ((hf_int.add hg_int).div_const 2) (hf_meas.mul hg_meas)
  filter_upwards with x
  simp only [Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply]
  calc |f x * g x| ≤ ((f x)^2 + (g x)^2) / 2 := by
        rw [abs_mul]; nlinarith [sq_abs (f x), sq_abs (g x), sq_nonneg (|f x| - |g x|)]
    _ ≤ |((f x)^2 + (g x)^2) / 2| := le_abs_self _

lemma sqrt_integral_sq_add_le
    {f g : α → ℝ}
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x)
    (hf_int : Integrable (fun x => (f x)^2) μ)
    (hg_int : Integrable (fun x => (g x)^2) μ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hg_meas : AEStronglyMeasurable g μ) :
    Real.sqrt (∫ x, (f x + g x)^2 ∂μ) ≤
      Real.sqrt (∫ x, (f x)^2 ∂μ) + Real.sqrt (∫ x, (g x)^2 ∂μ) := by
  set A := Real.sqrt (∫ x, (f x)^2 ∂μ)
  set B := Real.sqrt (∫ x, (g x)^2 ∂μ)
  rw [← Real.sqrt_sq (by positivity : 0 ≤ A + B)]
  apply Real.sqrt_le_sqrt
  have hA_sq : A^2 = ∫ x, (f x)^2 ∂μ :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x)))
  have hB_sq : B^2 = ∫ x, (g x)^2 ∂μ :=
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))
  have hfg_int : Integrable (fun x => f x * g x) μ :=
    integrable_mul_of_sq_integrable hf_int hg_int hf_meas hg_meas
  have h_cs : ∫ x, (f x * g x) ∂μ ≤ A * B :=
    cauchy_schwarz_integral hf_nn hg_nn hf_int hg_int hf_meas hg_meas
  have h_split : ∫ x, (f x + g x)^2 ∂μ =
      ∫ x, (f x)^2 ∂μ + 2 * ∫ x, (f x * g x) ∂μ + ∫ x, (g x)^2 ∂μ := by
    have h1 : ∀ x, (f x + g x)^2 = (f x)^2 + 2 * (f x * g x) + (g x)^2 := fun x => by ring
    simp_rw [h1]
    have i1 : ∫ x, ((f x)^2 + 2 * (f x * g x) + (g x)^2) ∂μ =
        ∫ x, ((f x)^2 + 2 * (f x * g x)) ∂μ + ∫ x, (g x)^2 ∂μ :=
      integral_add (hf_int.add (hfg_int.const_mul 2)) hg_int
    have i2 : ∫ x, ((f x)^2 + 2 * (f x * g x)) ∂μ =
        ∫ x, (f x)^2 ∂μ + ∫ x, 2 * (f x * g x) ∂μ :=
      integral_add hf_int (hfg_int.const_mul 2)
    have i3 : ∫ x, 2 * (f x * g x) ∂μ = 2 * ∫ x, f x * g x ∂μ :=
      integral_const_mul ..
    linarith
  linarith [h_cs, hA_sq, hB_sq]

lemma sqrt_integral_sq_mul (c : ℝ) (hc : 0 ≤ c) (f : α → ℝ) :
    Real.sqrt (∫ x, (c * f x)^2 ∂μ) = c * Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  simp_rw [show ∀ x, (c * f x)^2 = c^2 * (f x)^2 from fun x => by ring]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma memLp_two_weighted (w : ℝ) (f : α → ℝ)
    (hf_int : Integrable (fun x => (f x)^2) μ)
    (hf_meas : AEStronglyMeasurable f μ) :
    MemLp (fun x => w * f x) 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm (hf_meas.const_mul w)]
  convert (hf_int.const_mul (w^2)) using 1
  ext x; simp [mul_pow, Real.norm_eq_abs, sq_abs]

lemma memLp_two_weighted_sum {n : ℕ} (w : Fin n → ℝ) (f : Fin n → α → ℝ)
    (hf_int : ∀ j, Integrable (fun x => (f j x)^2) μ)
    (hf_meas : ∀ j, AEStronglyMeasurable (f j) μ) :
    MemLp (fun x => ∑ j : Fin n, w j * f j x) 2 μ := by
  induction n with
  | zero => simp only [Fin.sum_univ_zero]; exact MemLp.zero
  | succ n ih =>
    simp_rw [Fin.sum_univ_castSucc]
    exact (ih _ _ (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)).add
      (memLp_two_weighted _ _ (hf_int _) (hf_meas _))

lemma integrable_sq_of_memLp_two {f : α → ℝ} (hf : MemLp f 2 μ) :
    Integrable (fun x => (f x)^2) μ :=
  MemLp.integrable_sq hf

/-- **Minkowski inequality for weighted L² sums** (proved theorem)

    For nonneg weights wⱼ and nonneg functions fⱼ with fⱼ² integrable:
    √(∫ (∑ⱼ wⱼfⱼ)² dμ) ≤ ∑ⱼ wⱼ √(∫ fⱼ² dμ)

    Proof by induction on n, using Cauchy-Schwarz for integrals at each step. -/
theorem minkowski_weighted_L2_sum_proved {n : ℕ} {w : Fin n → ℝ} {f : Fin n → α → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hf : ∀ j ω, 0 ≤ f j ω)
    (hf_int : ∀ j, Integrable (fun ω => (f j ω)^2) μ)
    (hf_meas : ∀ j, AEStronglyMeasurable (f j) μ) :
    Real.sqrt (∫ ω, (∑ j, w j * f j ω)^2 ∂μ) ≤ ∑ j, w j * Real.sqrt (∫ ω, (f j ω)^2 ∂μ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [Fin.sum_univ_castSucc]
    set S := fun ω => ∑ j : Fin n, w j.castSucc * f j.castSucc ω
    set g := fun ω => w (Fin.last n) * f (Fin.last n) ω
    have hS_nn : ∀ ω, 0 ≤ S ω := fun ω =>
      Finset.sum_nonneg (fun j _ => mul_nonneg (hw j.castSucc) (hf j.castSucc ω))
    have hg_nn : ∀ ω, 0 ≤ g ω := fun ω => mul_nonneg (hw _) (hf _ ω)
    have hS_memLp : MemLp S 2 μ :=
      memLp_two_weighted_sum _ _ (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)
    have hg_memLp : MemLp g 2 μ :=
      memLp_two_weighted _ _ (hf_int _) (hf_meas _)
    have hS_int : Integrable (fun ω => (S ω)^2) μ := integrable_sq_of_memLp_two hS_memLp
    have hg_int : Integrable (fun ω => (g ω)^2) μ := integrable_sq_of_memLp_two hg_memLp
    calc Real.sqrt (∫ ω, (S ω + g ω)^2 ∂μ)
        ≤ Real.sqrt (∫ ω, (S ω)^2 ∂μ) + Real.sqrt (∫ ω, (g ω)^2 ∂μ) :=
          sqrt_integral_sq_add_le hS_nn hg_nn hS_int hg_int
            hS_memLp.aestronglyMeasurable hg_memLp.aestronglyMeasurable
      _ ≤ (∑ j : Fin n, w j.castSucc * Real.sqrt (∫ ω, (f j.castSucc ω)^2 ∂μ)) +
          (w (Fin.last n) * Real.sqrt (∫ ω, (f (Fin.last n) ω)^2 ∂μ)) := by
          gcongr
          · exact ih (fun j => hw j.castSucc) (fun j => hf j.castSucc)
              (fun j => hf_int j.castSucc) (fun j => hf_meas j.castSucc)
          · exact le_of_eq (sqrt_integral_sq_mul _ (hw _) _)

end Minkowski

end

end OSforGFF

end L2TimeIntegral

/-! ### From `General/FourierTransforms.lean` (moved 2026-08-30) -/

section FourierTransformsTripleReorder

open MeasureTheory MeasureTheory.Measure

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]

/-- The permutation map (x, (y, k)) ↦ (k, (x, y)) as a measurable equivalence.
    Constructed by composing prodAssoc.symm (reassociating) with prodComm (swapping). -/
noncomputable def tripleReorder : α × (α × α) ≃ᵐ α × (α × α) :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

/-- The tripleReorder map is measure-preserving on product Lebesgue measures. -/
lemma measurePreserving_tripleReorder :
    MeasurePreserving (tripleReorder (α := α))
      ((volume : Measure α).prod (volume.prod volume))
      ((volume : Measure α).prod (volume.prod volume)) := by
  unfold tripleReorder
  have h1 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := α) (γ := α)).symm
      ((volume : Measure α).prod (volume.prod volume))
      ((volume.prod volume).prod volume) :=
    (measurePreserving_prodAssoc volume volume volume).symm MeasurableEquiv.prodAssoc
  have h2 : MeasurePreserving (MeasurableEquiv.prodComm (α := α × α) (β := α))
      (((volume : Measure α).prod volume).prod volume)
      ((volume : Measure α).prod (volume.prod volume)) :=
    MeasureTheory.Measure.measurePreserving_swap
  exact h2.comp h1

end FourierTransformsTripleReorder

/-! ### From `General/FunctionalAnalysis.lean` (moved 2026-08-30): the Lp measure-lifting
chain -/

section LiftMeasure

open MeasureTheory MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Postcomposition with `Complex.ofRealCLM` is continuous `Lp ℝ 2 μ → Lp ℂ 2 μ`. -/
lemma Complex.ofRealCLM_continuous_compLp :
  Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) :=
  (ContinuousLinearMap.compLpL 2 μ Complex.ofRealCLM).continuous

/--
Compose an Lp function with a continuous linear map.
This should be the canonical way to lift real Lp functions to complex Lp functions.
-/
noncomputable def composed_function (f : Lp ℝ 2 μ) (A : ℝ →L[ℝ] ℂ) : Lp ℂ 2 μ :=
  A.compLp f

/--
Embedding from real Lp functions to complex Lp functions using the canonical embedding ℝ → ℂ.
-/
noncomputable def embedding_real_to_complex (φ : Lp ℝ 2 μ) : Lp ℂ 2 μ :=
  composed_function φ (Complex.ofRealCLM)

/--
Lifts a probability measure from the space of real Lp functions to the space of
complex Lp functions, with support on the real subspace.
-/
noncomputable def liftMeasure_real_to_complex
    (dμ_real : ProbabilityMeasure (Lp ℝ 2 μ)) :
    ProbabilityMeasure (Lp ℂ 2 μ) :=
  let dμ_complex_measure : Measure (Lp ℂ 2 μ) :=
    Measure.map embedding_real_to_complex dμ_real
  have h_ae : AEMeasurable embedding_real_to_complex dμ_real := by
    apply Continuous.aemeasurable
    unfold embedding_real_to_complex composed_function
    have : Continuous (fun φ : Lp ℝ 2 μ => Complex.ofRealCLM.compLp φ : Lp ℝ 2 μ → Lp ℂ 2 μ) :=
      Complex.ofRealCLM_continuous_compLp
    exact this
  have h_is_prob := isProbabilityMeasure_map h_ae
  ⟨dμ_complex_measure, h_is_prob⟩

end LiftMeasure

/-! ### From `Covariance/RealForm.lean` (moved 2026-08-30) -/

section CovarianceRealForm

open MeasureTheory MeasureTheory.Measure

namespace QFT

variable {d : ℕ}

/-- The weighted measure on momentum space with density (‖k‖² + m²)⁻¹. -/
noncomputable def momentumWeightMeasure (m : ℝ) : Measure (SpaceTime d) :=
  volume.withDensity (fun k => ENNReal.ofReal (1 / (‖k‖ ^ 2 + m ^ 2)))

end QFT

end CovarianceRealForm
