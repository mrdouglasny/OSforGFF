import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import OSforGFF.Basic
import OSforGFF.NuclearSpace.PhysHermiteSchwartz
import OSforGFF.NuclearSpace.RapidDecaySeqMulti

/-!
# PhysLean Hermite data on spacetime `SpaceTime = ℝ⁴`

This file provides a small amount of infrastructure needed for the Hermite-expansion approach to
the nuclearity of `TestFunction = 𝓢(SpaceTime, ℝ)`:

* a canonical decoding `ℕ → ℕ × ℕ × ℕ × ℕ` compatible with `RapidDecaySeqMulti.pairEquiv₄`;
* the corresponding (unnormalized) 4D harmonic-oscillator eigenfunctions as functions
  `SpaceTime → ℝ`;
* their coefficient functionals on `TestFunction`, defined as continuous linear maps via
  `SchwartzMap.smulLeftCLM` and `SchwartzMap.integralCLM`.

At this stage we only set up the API and continuity; orthogonality/completeness and the resulting
topological isomorphism to a rapid-decay sequence model will be developed in subsequent files.
-/

open scoped BigOperators ENNReal InnerProductSpace RealInnerProductSpace

namespace PhysLean

noncomputable section

open MeasureTheory
open SchwartzMap

namespace SpaceTimeHermite

/-! ## Decoding `ℕ` into four indices -/

/-- Decode `n : ℕ` into a 4-tuple of natural numbers, using `RapidDecaySeqMulti.pairEquiv₄`. -/
def unpair₄ (n : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm n

@[simp] lemma unpair₄_apply (n : ℕ) :
    unpair₄ n = OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm n := rfl

abbrev unpair₄₁ (n : ℕ) : ℕ := (unpair₄ n).1.1
abbrev unpair₄₂ (n : ℕ) : ℕ := (unpair₄ n).1.2
abbrev unpair₄₃ (n : ℕ) : ℕ := (unpair₄ n).2.1
abbrev unpair₄₄ (n : ℕ) : ℕ := (unpair₄ n).2.2

/-! ## Helper: the multi-index components as a function `Fin 4 → ℕ` -/

/-- The `i`-th component of the 4-tuple `unpair₄ n`, with indices ordered as `0,1,2,3`. -/
def idx (n : ℕ) : Fin STDimension → ℕ
  | ⟨0, _⟩ => unpair₄₁ n
  | ⟨1, _⟩ => unpair₄₂ n
  | ⟨2, _⟩ => unpair₄₃ n
  | ⟨3, _⟩ => unpair₄₄ n

@[simp] lemma idx_zero (n : ℕ) : idx n 0 = unpair₄₁ n := by rfl
@[simp] lemma idx_one (n : ℕ) : idx n 1 = unpair₄₂ n := by rfl
@[simp] lemma idx_two (n : ℕ) : idx n 2 = unpair₄₃ n := by rfl
@[simp] lemma idx_three (n : ℕ) : idx n 3 = unpair₄₄ n := by rfl

lemma base₄_eq_unpair₄ (n : ℕ) :
    OSforGFF.RapidDecaySeqMulti.base₄ n =
      (((unpair₄₁ n + 1 : ℕ) : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) *
        (((unpair₄₃ n + 1 : ℕ) : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) := by
  -- this is just unpacking `RapidDecaySeqMulti.base₄` along our `unpair₄` notation
  simp [OSforGFF.RapidDecaySeqMulti.base₄, unpair₄, unpair₄₁, unpair₄₂, unpair₄₃, unpair₄₄]

/-! ## The 4D eigenfunctions (as plain functions) -/

/-- Coordinate projection `SpaceTime →L[ℝ] ℝ`. -/
abbrev coordCLM (i : Fin STDimension) : SpaceTime →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin STDimension) i)

@[simp] lemma coordCLM_apply (i : Fin STDimension) (x : SpaceTime) :
    coordCLM i x = x i := by
  -- `EuclideanSpace.proj` is the coordinate projection.
  simp [coordCLM]

@[simp] lemma coordCLM_toLp (i : Fin STDimension) (v : Fin STDimension → ℝ) :
    coordCLM i (WithLp.toLp (2 : ℝ≥0∞) v) = v i := by
  simp [coordCLM]

/-- The (unnormalized) 4D harmonic-oscillator eigenfunction indexed by `n : ℕ`, built as a product
of 1D `eigenfunctionRealSchwartz` along coordinates. -/
def eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) : ℝ :=
  (eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x))
    * (eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x))
    * (eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x))
    * (eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x))

lemma eigenfunctionRealSpaceTime_eq_prod (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    eigenfunctionRealSpaceTime ξ hξ n x =
      ∏ i : Fin STDimension, eigenfunctionRealSchwartz ξ hξ (idx n i) (coordCLM i x) := by
  classical
  -- `STDimension = 4`, so this is just a finite product over `{0,1,2,3}`.
  simp [eigenfunctionRealSpaceTime, idx, Fin.prod_univ_four]

lemma eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Function.HasTemperateGrowth (eigenfunctionRealSpaceTime ξ hξ n) := by
  classical
  have ht :
      Function.HasTemperateGrowth (fun x : SpaceTime ↦
        (eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x))
          * (eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x))
          * (eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x))
          * (eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x))) := by
    fun_prop
  simpa [eigenfunctionRealSpaceTime, -eigenfunctionRealSchwartz_apply] using ht

/-! ## Coefficient functionals on `TestFunction` -/

/-- The coefficient functional on `TestFunction` against the 4D eigenfunction indexed by `n`. -/
noncomputable def coeffCLM_SpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    TestFunction →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM (𝕜 := ℝ) (μ := (volume : Measure SpaceTime))).comp
    (SchwartzMap.smulLeftCLM (F := ℝ) (eigenfunctionRealSpaceTime ξ hξ n))

@[simp] lemma coeffCLM_SpaceTime_apply (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    coeffCLM_SpaceTime ξ hξ n f =
      ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * f x := by
  have hg : (eigenfunctionRealSpaceTime ξ hξ n).HasTemperateGrowth :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) (n := n)
  simp [coeffCLM_SpaceTime, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) hg, smul_eq_mul]

/-- The coefficient map `TestFunction → (ℕ → ℝ)`, sending `f` to its Hermite coefficients. -/
noncomputable def coeffCLM_SpaceTime_pi (ξ : ℝ) (hξ : ξ ≠ 0) : TestFunction →L[ℝ] (ℕ → ℝ) :=
  ContinuousLinearMap.pi (fun n : ℕ => coeffCLM_SpaceTime ξ hξ n)

@[simp] lemma coeffCLM_SpaceTime_pi_apply (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) (n : ℕ) :
    coeffCLM_SpaceTime_pi ξ hξ f n = coeffCLM_SpaceTime ξ hξ n f := by
  rfl

lemma coeffCLM_SpaceTime_pi_apply' (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ℕ => ℝ) n).comp (coeffCLM_SpaceTime_pi ξ hξ)
      = coeffCLM_SpaceTime ξ hξ n := by
  -- componentwise: projections after `pi` recover the original family
  ext f
  rfl

/-! ## `L²`-orthogonality and norm factorization -/

lemma integral_eigenfunctionRealSpaceTime_mul_eq_prod (ξ : ℝ) (hξ : ξ ≠ 0) (n m : ℕ) :
    ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ m x =
      ∏ i : Fin STDimension, ∫ t : ℝ, eigenfunctionReal ξ (idx n i) t * eigenfunctionReal ξ (idx m i) t := by
  classical
  -- Change variables along the measure-preserving identification `toLp : (Fin 4 → ℝ) → SpaceTime`.
  have hmp : MeasurePreserving (WithLp.toLp (2 : ℝ≥0∞) : (Fin STDimension → ℝ) → SpaceTime) :=
    PiLp.volume_preserving_toLp (Fin STDimension)
  -- Use the `MeasurePreserving.integral_comp` lemma in the direction `SpaceTime → (Fin 4 → ℝ)`.
  rw [← hmp.integral_comp (MeasurableEquiv.toLp (2 : ℝ≥0∞) (Fin STDimension → ℝ)).measurableEmbedding
    (g := fun x : SpaceTime ↦
      eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ m x)]
  -- Now apply Fubini on the finite product.
  -- The integrand factors as a product of 1D terms along coordinates.
  have hfac :
      (fun v : Fin STDimension → ℝ ↦
        eigenfunctionRealSpaceTime ξ hξ n (WithLp.toLp (2 : ℝ≥0∞) v) *
          eigenfunctionRealSpaceTime ξ hξ m (WithLp.toLp (2 : ℝ≥0∞) v))
        =
      (fun v : Fin STDimension → ℝ ↦
        ∏ i : Fin STDimension, (eigenfunctionReal ξ (idx n i) (v i) * eigenfunctionReal ξ (idx m i) (v i))) := by
    funext v
    -- Expand both sides via the `Fin`-product expression of `eigenfunctionRealSpaceTime`.
    have hn :
        eigenfunctionRealSpaceTime ξ hξ n (WithLp.toLp (2 : ℝ≥0∞) v) =
          ∏ i : Fin STDimension, eigenfunctionReal ξ (idx n i) (v i) := by
      -- use `eigenfunctionRealSpaceTime_eq_prod` and simplify coordinates
      simp [eigenfunctionRealSpaceTime_eq_prod, eigenfunctionRealSchwartz_apply]
    have hm :
        eigenfunctionRealSpaceTime ξ hξ m (WithLp.toLp (2 : ℝ≥0∞) v) =
          ∏ i : Fin STDimension, eigenfunctionReal ξ (idx m i) (v i) := by
      simp [eigenfunctionRealSpaceTime_eq_prod, eigenfunctionRealSchwartz_apply]
    -- Combine and use `Finset.prod_mul_distrib` to regroup.
    simp [hn, hm, Finset.prod_mul_distrib, mul_assoc]
  -- Substitute the factored integrand and compute the integral as a product of 1D integrals.
  rw [hfac]
  -- Fubini for a finite product of Lebesgue measures
  simpa using (MeasureTheory.integral_fintype_prod_volume_eq_prod
    (ι := Fin STDimension) (f := fun i (t : ℝ) ↦ eigenfunctionReal ξ (idx n i) t * eigenfunctionReal ξ (idx m i) t))

private lemma exists_idx_ne_of_ne {n m : ℕ} (hnm : n ≠ m) :
    ∃ i : Fin STDimension, idx n i ≠ idx m i := by
  classical
  by_contra h
  push_neg at h
  have h0 : unpair₄₁ n = unpair₄₁ m := by simpa using h 0
  have h1 : unpair₄₂ n = unpair₄₂ m := by simpa using h 1
  have h2 : unpair₄₃ n = unpair₄₃ m := by simpa using h 2
  have h3 : unpair₄₄ n = unpair₄₄ m := by simpa using h 3
  have hunpair : unpair₄ n = unpair₄ m := by
    ext
    · simpa [unpair₄₁] using h0
    · simpa [unpair₄₂] using h1
    · simpa [unpair₄₃] using h2
    · simpa [unpair₄₄] using h3
  -- `unpair₄` is the inverse of an equivalence, hence injective.
  exact hnm <| by
    -- apply the equivalence `pairEquiv₄` to both sides
    simpa [unpair₄] using congrArg OSforGFF.RapidDecaySeqMulti.pairEquiv₄ hunpair

lemma integral_eigenfunctionRealSpaceTime_orthogonal (ξ : ℝ) (hξ : ξ ≠ 0) {n m : ℕ} (hnm : n ≠ m) :
    ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ m x = 0 := by
  classical
  -- Factor as a product of 1D integrals and use 1D orthogonality.
  rw [integral_eigenfunctionRealSpaceTime_mul_eq_prod (ξ := ξ) (hξ := hξ) (n := n) (m := m)]
  rcases exists_idx_ne_of_ne (n := n) (m := m) hnm with ⟨i, hi⟩
  have hfactor :
      (∫ t : ℝ, eigenfunctionReal ξ (idx n i) t * eigenfunctionReal ξ (idx m i) t) = 0 := by
    simpa [mul_assoc] using (eigenfunctionReal_orthogonal (ξ := ξ) (n := idx n i) (m := idx m i) hi)
  -- One factor is zero, hence the finite product is zero.
  have : (∏ j : Fin STDimension,
      ∫ t : ℝ, eigenfunctionReal ξ (idx n j) t * eigenfunctionReal ξ (idx m j) t) = 0 := by
    -- rewrite the `Fintype` product as a `Finset` product and apply `Finset.prod_eq_zero`.
    classical
    simpa using
      (Finset.prod_eq_zero (s := (Finset.univ : Finset (Fin STDimension)))
        (f := fun j : Fin STDimension ↦
          ∫ t : ℝ, eigenfunctionReal ξ (idx n j) t * eigenfunctionReal ξ (idx m j) t)
        (hi := by simp) hfactor)
  simpa using this

lemma integral_eigenfunctionRealSpaceTime_self (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x =
      ∏ i : Fin STDimension, (|ξ| * (↑(idx n i).factorial * 2 ^ (idx n i) * √Real.pi)) := by
  -- factor the 4D integral into a product of 1D integrals, then use the 1D norm formula
  rw [integral_eigenfunctionRealSpaceTime_mul_eq_prod (ξ := ξ) (hξ := hξ) (n := n) (m := n)]
  -- simplify each factor using `eigenfunctionReal_norm`
  refine Finset.prod_congr rfl ?_
  intro i hi
  -- turn scalar multiplication into multiplication in `ℝ`
  simpa [smul_eq_mul] using (eigenfunctionReal_norm (ξ := ξ) (n := idx n i))

/-! ## Normalization in `L²` and Bessel bounds on coefficients -/

/-- The squared `L²`-norm constant of the unnormalized spacetime eigenfunction. -/
noncomputable def normConstSpaceTime (ξ : ℝ) (n : ℕ) : ℝ :=
  ∏ i : Fin STDimension, (|ξ| * (↑(idx n i).factorial * 2 ^ (idx n i) * √Real.pi))

@[simp] lemma normConstSpaceTime_def (ξ : ℝ) (n : ℕ) :
    normConstSpaceTime ξ n =
      ∏ i : Fin STDimension, (|ξ| * (↑(idx n i).factorial * 2 ^ (idx n i) * √Real.pi)) := rfl

lemma normConstSpaceTime_pos (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) : 0 < normConstSpaceTime ξ n := by
  classical
  -- each factor is positive
  have hξ' : 0 < |ξ| := abs_pos.2 hξ
  have hpi : 0 < (√Real.pi : ℝ) := by
    simpa using Real.sqrt_pos.2 Real.pi_pos
  refine Finset.prod_pos ?_
  intro i hi
  have hfac : 0 < (↑(idx n i).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (idx n i)
  have hpow : 0 < (2 : ℝ) ^ (idx n i) := by
    exact pow_pos (by norm_num : (0 : ℝ) < 2) (idx n i)
  -- combine
  have hmul : 0 < (↑(idx n i).factorial * 2 ^ (idx n i) : ℝ) :=
    mul_pos hfac hpow
  have hmul' : 0 < (↑(idx n i).factorial * 2 ^ (idx n i) * √Real.pi : ℝ) :=
    mul_pos hmul hpi
  exact mul_pos hξ' hmul'

lemma integral_eigenfunctionRealSpaceTime_self_eq_normConstSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x =
      normConstSpaceTime ξ n := by
  simpa [normConstSpaceTime] using (integral_eigenfunctionRealSpaceTime_self (ξ := ξ) (hξ := hξ) n)

lemma integrable_eigenfunctionRealSpaceTime_mul_self (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Integrable
      (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x)
      (volume : Measure SpaceTime) := by
  -- if not integrable, the integral is `0`, contradicting the explicit positive value
  by_contra h
  have h0 :
      (∫ x : SpaceTime,
          eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x) = 0 := by
    simp [MeasureTheory.integral_undef h]
  have hpos : 0 < (∫ x : SpaceTime,
          eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x) := by
    -- rewrite using the closed form
    rw [integral_eigenfunctionRealSpaceTime_self_eq_normConstSpaceTime (ξ := ξ) (hξ := hξ) (n := n)]
    exact normConstSpaceTime_pos (ξ := ξ) hξ n
  exact (ne_of_gt hpos) h0

lemma continuous_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    Continuous (eigenfunctionRealSpaceTime ξ hξ n) := by
  -- `HasTemperateGrowth` gives `C^∞`, hence continuity.
  have ht : Function.HasTemperateGrowth (eigenfunctionRealSpaceTime ξ hξ n) :=
    eigenfunctionRealSpaceTime_hasTemperateGrowth (ξ := ξ) (hξ := hξ) n
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (eigenfunctionRealSpaceTime ξ hξ n) :=
    (Function.hasTemperateGrowth_iff_isBigO).1 ht |>.1
  exact hcd.continuous

lemma aestronglyMeasurable_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    AEStronglyMeasurable (eigenfunctionRealSpaceTime ξ hξ n) (volume : Measure SpaceTime) := by
  exact (continuous_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n)).aestronglyMeasurable

lemma memLp_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    MemLp (eigenfunctionRealSpaceTime ξ hξ n) 2 (volume : Measure SpaceTime) := by
  have hmeas :
      AEStronglyMeasurable (eigenfunctionRealSpaceTime ξ hξ n) (volume : Measure SpaceTime) :=
    aestronglyMeasurable_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n)
  have hint :
      Integrable (fun x : SpaceTime ↦ (eigenfunctionRealSpaceTime ξ hξ n x) ^ 2)
        (volume : Measure SpaceTime) := by
    -- `x ↦ f x ^ 2 = f x * f x`
    simpa [pow_two] using
      (integrable_eigenfunctionRealSpaceTime_mul_self (ξ := ξ) (hξ := hξ) (n := n))
  exact (MeasureTheory.memLp_two_iff_integrable_sq (μ := (volume : Measure SpaceTime)) hmeas).2 hint

/-- The unnormalized spacetime eigenfunction as an element of `L²(SpaceTime)`. -/
noncomputable def eigenfunctionRealSpaceTimeL2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    SpaceTime →₂[(volume : Measure SpaceTime)] ℝ :=
  (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp (eigenfunctionRealSpaceTime ξ hξ n)

lemma inner_eigenfunctionRealSpaceTimeL2_eq_integral (ξ : ℝ) (hξ : ξ ≠ 0) (n m : ℕ) :
    ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ m⟫ =
      ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ m x := by
  -- unfold the `L²` inner product and rewrite using the `toLp` representatives
  classical
  simp only [eigenfunctionRealSpaceTimeL2, MeasureTheory.L2.inner_def]
  -- replace the `toLp` representatives by the original functions
  refine integral_congr_ae ?_
  have hn_ae :
      (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp
          (eigenfunctionRealSpaceTime ξ hξ n) =ᵐ[(volume : Measure SpaceTime)]
        eigenfunctionRealSpaceTime ξ hξ n :=
    (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).coeFn_toLp
  have hm_ae :
      (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) m).toLp
          (eigenfunctionRealSpaceTime ξ hξ m) =ᵐ[(volume : Measure SpaceTime)]
        eigenfunctionRealSpaceTime ξ hξ m :=
    (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) m).coeFn_toLp
  filter_upwards [hn_ae, hm_ae] with x hx hy
  simp [hx, hy, mul_comm]

/-- The normalized spacetime eigenfunctions in `L²(SpaceTime)`. -/
noncomputable def normalizedEigenfunctionSpaceTimeL2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) :
    SpaceTime →₂[(volume : Measure SpaceTime)] ℝ :=
  (Real.sqrt (normConstSpaceTime ξ n))⁻¹ • eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n

lemma orthonormal_normalizedEigenfunctionSpaceTimeL2 (ξ : ℝ) (hξ : ξ ≠ 0) :
    Orthonormal ℝ (normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ) := by
  classical
  -- use the Kronecker-delta characterization
  refine (orthonormal_iff_ite (𝕜 := ℝ) (v := normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)).2 ?_
  intro n m
  by_cases hnm : n = m
  · subst hnm
    -- diagonal: compute the inner product and cancel the normalization
    have hpos : 0 < normConstSpaceTime ξ n := normConstSpaceTime_pos (ξ := ξ) hξ n
    have hsqrt : (Real.sqrt (normConstSpaceTime ξ n)) ≠ 0 := (Real.sqrt_ne_zero').2 hpos
    have hinner :
        ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n⟫ =
          normConstSpaceTime ξ n := by
      -- rewrite the `L²` inner product as an explicit integral, then use the closed form
      have hN :
          (∫ x : SpaceTime,
              eigenfunctionRealSpaceTime ξ hξ n x * eigenfunctionRealSpaceTime ξ hξ n x) =
            normConstSpaceTime ξ n := by
        simpa using
          (integral_eigenfunctionRealSpaceTime_self_eq_normConstSpaceTime (ξ := ξ) (hξ := hξ) (n := n))
      -- combine (use `rw`, not `simp`, to avoid rewriting `⟪x,x⟫` into `‖x‖^2`)
      rw [inner_eigenfunctionRealSpaceTimeL2_eq_integral (ξ := ξ) (hξ := hξ) (n := n) (m := n)]
      exact hN
    -- reduce the RHS `if` and unfold the normalization scalar
    rw [if_pos rfl]
    dsimp [normalizedEigenfunctionSpaceTimeL2]
    -- pull out the scalar normalization factors
    rw [inner_smul_left, inner_smul_right]
    -- use the closed form for the unnormalized inner product before simplification
    rw [hinner]
    -- `ℝ` has trivial conjugation
    simp
    -- clear denominators and simplify `√N * √N = N`
    field_simp [hsqrt]
    -- normalize the products inside the square roots (commutativity/associativity)
    have hprod :
        (∏ i : Fin STDimension, |ξ| * √Real.pi * (↑(idx n i).factorial) * 2 ^ idx n i) =
          ∏ i : Fin STDimension, |ξ| * (↑(idx n i).factorial) * 2 ^ idx n i * √Real.pi := by
      classical
      refine Finset.prod_congr rfl ?_
      intro i hi
      simp [mul_assoc, mul_left_comm, mul_comm]
    rw [hprod]
    have hnonneg :
        0 ≤ (∏ i : Fin STDimension, |ξ| * (↑(idx n i).factorial) * 2 ^ idx n i * √Real.pi) := by
      have : 0 ≤ normConstSpaceTime ξ n := le_of_lt hpos
      simpa [normConstSpaceTime, mul_assoc, mul_left_comm, mul_comm] using this
    symm
    simpa using (Real.mul_self_sqrt hnonneg)
  · -- off-diagonal: orthogonality survives normalization
    have hnm' : n ≠ m := hnm
    rw [if_neg hnm']
    dsimp [normalizedEigenfunctionSpaceTimeL2]
    rw [inner_smul_left, inner_smul_right]
    simp
    have horth :
        ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ m⟫ = 0 := by
      rw [inner_eigenfunctionRealSpaceTimeL2_eq_integral (ξ := ξ) (hξ := hξ) (n := n) (m := m)]
      simpa using
        (integral_eigenfunctionRealSpaceTime_orthogonal (ξ := ξ) (hξ := hξ) (hnm := hnm'))
    simp [horth]

lemma inner_eigenfunctionRealSpaceTimeL2_toLp_eq_coeffCLM_SpaceTime (ξ : ℝ) (hξ : ξ ≠ 0)
    (n : ℕ) (f : TestFunction) :
    ⟪eigenfunctionRealSpaceTimeL2 (ξ := ξ) hξ n, f.toLp 2 (volume : Measure SpaceTime)⟫ =
      coeffCLM_SpaceTime ξ hξ n f := by
  -- unfold the `L²` inner product and replace representatives by the original functions
  classical
  simp only [eigenfunctionRealSpaceTimeL2, MeasureTheory.L2.inner_def]
  have hn_ae :
      (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp
          (eigenfunctionRealSpaceTime ξ hξ n) =ᵐ[(volume : Measure SpaceTime)]
        eigenfunctionRealSpaceTime ξ hξ n :=
    (memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).coeFn_toLp
  have hf_ae :
      f.toLp 2 (volume : Measure SpaceTime) =ᵐ[(volume : Measure SpaceTime)] f :=
    SchwartzMap.coeFn_toLp f 2 (volume : Measure SpaceTime)
  have hcongr :
      (fun x : SpaceTime ↦
          ⟪(memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp
              (eigenfunctionRealSpaceTime ξ hξ n) x,
            f.toLp 2 (volume : Measure SpaceTime) x⟫) =ᵐ[(volume : Measure SpaceTime)]
        (fun x : SpaceTime ↦ eigenfunctionRealSpaceTime ξ hξ n x * f x) := by
    filter_upwards [hn_ae, hf_ae] with x hx hf
    -- inner product on `ℝ` is multiplication (up to commutativity)
    simp [hx, hf, mul_comm]
  -- rewrite the integral using a.e. equality, then unfold the coefficient functional
  have hint :
      (∫ x : SpaceTime,
          ⟪(memLp_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) n).toLp
              (eigenfunctionRealSpaceTime ξ hξ n) x,
            f.toLp 2 (volume : Measure SpaceTime) x⟫) =
        ∫ x : SpaceTime, eigenfunctionRealSpaceTime ξ hξ n x * f x := by
    simpa using (MeasureTheory.integral_congr_ae (μ := (volume : Measure SpaceTime)) hcongr)
  -- the right-hand side is the defining integral for the coefficient functional
  simpa [coeffCLM_SpaceTime_apply] using hint

lemma inner_normalizedEigenfunctionSpaceTimeL2_toLp (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    ⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n, f.toLp 2 (volume : Measure SpaceTime)⟫ =
      (Real.sqrt (normConstSpaceTime ξ n))⁻¹ * coeffCLM_SpaceTime ξ hξ n f := by
  -- expand the inner product and use the coefficient-inner identification
  simp [normalizedEigenfunctionSpaceTimeL2, inner_smul_left,
    inner_eigenfunctionRealSpaceTimeL2_toLp_eq_coeffCLM_SpaceTime (ξ := ξ) (hξ := hξ) (n := n) (f := f),
    mul_assoc]

lemma summable_sq_inner_normalizedEigenfunctionSpaceTimeL2 (ξ : ℝ) (hξ : ξ ≠ 0) (f : TestFunction) :
    Summable (fun n : ℕ =>
      ‖⟪normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ n, f.toLp 2 (volume : Measure SpaceTime)⟫‖ ^ 2) := by
  -- Bessel inequality for an orthonormal family in a Hilbert space
  simpa using
    (Orthonormal.inner_products_summable (𝕜 := ℝ)
      (v := normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ)
      (x := f.toLp 2 (volume : Measure SpaceTime))
      (orthonormal_normalizedEigenfunctionSpaceTimeL2 (ξ := ξ) hξ))

end SpaceTimeHermite

end

end PhysLean

