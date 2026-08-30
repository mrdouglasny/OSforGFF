/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Measure.GaussianFreeField
import OSforGFF.Instances.Dim2
import OSforGFF.Instances.Dim3
import OSforGFF.Instances.Dim4
import OSforGFF.Instances.Dim5
import OSforGFF.OS.OS3_ReflectionPositivity
import OSforGFF.OS.OS0_Analyticity
import OSforGFF.OS.OS1_Regularity
import OSforGFF.OS.OS2_Invariance
import OSforGFF.OS.OS4_Clustering
import OSforGFF.OS.OS4_Ergodicity

/-!
# Master Theorem

Assembles OS0–OS4 into the dimension-generic
`gaussianFreeField_satisfies_all_OS_axioms_generic`, the all-dimensions corollary
`gaussianFreeField_satisfies_all_OS_axioms_of_dim` (every `d ≥ 2`, via the canonical
`GFFPropagator.ofProperTime`), and the concrete instances
`gaussianFreeField_satisfies_all_OS_axioms_dim2` (K₀),
`gaussianFreeField_satisfies_all_OS_axioms_dim3` (Yukawa),
`gaussianFreeField_satisfies_all_OS_axioms_dim4` (Bessel K₁), and
`gaussianFreeField_satisfies_all_OS_axioms_dim5` (K_{3/2}). The generic theorem is proved by:

- OS0 (Analyticity): Hartogs + Fernique — `OS.OS0_Analyticity`
- OS1 (Regularity): Plancherel + momentum bound — `OS.OS1_Regularity`
- OS2 (Euclidean Invariance): C depends on |x−y| — `OS.OS2_Invariance`
- OS3 (Reflection Positivity): Schwinger parametrization + Schur–Hadamard — `OS.OS3_ReflectionPositivity`
- OS4 (Clustering): Gaussian factorization + convolution decay — `OS.OS4_Clustering`
- OS4 (Ergodicity): polynomial clustering α=6 → L² convergence — `OS.OS4_Ergodicity`

The generic theorem holds for any spacetime dimension `d ≥ 2` equipped with a
`GFFPropagator d m` instance (the closed-form radial covariance identified with the
proper-time integral); the OS3 proper-time Fubini domination runs at boundary-vanishing
order `d`, so no upper bound on the dimension is needed.
-/

open scoped BigOperators

namespace OSforGFF

noncomputable section

/-! ## Master OS theorem for the free GFF -/

/-- Master theorem, dimension-generic form: the free GFF in dimension `d` (with
    `d ≥ 2` and a `GFFPropagator d m` instance) satisfies all
    Osterwalder–Schrader axioms.
- OS0 is supplied by `QFT.gaussianFreeField_satisfies_OS0` via the holomorphic integral theorem
- OS1 is supplied by `gaussianFreeField_satisfies_OS1` via Fourier/momentum space methods
- OS2 is supplied by `gaussian_satisfies_OS2` via Euclidean invariance of the free covariance
- OS3 is supplied by `QFT.gaussianFreeField_OS3` via the Schur-Hadamard argument (complex star formulation)
- OS4 Clustering is supplied by `QFT.gaussianFreeField_satisfies_OS4` via Gaussian factorization
- OS4 Ergodicity is supplied by polynomial clustering (α=6) → ergodicity -/
theorem gaussianFreeField_satisfies_all_OS_axioms_generic
    {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    SatisfiesAllOS (gaussianFreeField_free (d := d) m) where
  os0 := QFT.gaussianFreeField_satisfies_OS0 m
  os1 := gaussianFreeField_satisfies_OS1 m
  os2 := gaussian_satisfies_OS2 (gaussianFreeField_free (d := d) m)
    (by exact isGaussianGJ_gaussianFreeField_free m)
    (QFT.CovarianceEuclideanInvariantℂ_μ_GFF m)
  os3 := QFT.gaussianFreeField_OS3 m
  os4_clustering := QFT.gaussianFreeField_satisfies_OS4 m
  os4_ergodicity := OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity m
    (QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering m 6 (by norm_num))

/-- Master theorem, all-dimensions form: for every `d ≥ 2` the free GFF built from the
canonical proper-time propagator (`GFFPropagator.ofProperTime`) satisfies all
Osterwalder–Schrader axioms. This drops the `[GFFPropagator d m]` hypothesis of
`gaussianFreeField_satisfies_all_OS_axioms_generic` by supplying the canonical instance, so no
per-`d` closed form is needed; the concrete instances (`d = 2, 3, 4, 5`) additionally exhibit
the covariance in closed form. -/
theorem gaussianFreeField_satisfies_all_OS_axioms_of_dim (d : ℕ) [Fact (2 ≤ d)]
    (m : ℝ) [Fact (0 < m)] :
    letI := GFFPropagator.ofProperTime d m
    SatisfiesAllOS (gaussianFreeField_free (d := d) m) := by
  letI := GFFPropagator.ofProperTime d m
  exact gaussianFreeField_satisfies_all_OS_axioms_generic m

/-- Master theorem, two-dimensional instance: the free GFF with the Bessel covariance
`K₀(mr)/(2π)` satisfies all Osterwalder-Schrader axioms. This is the `d = 2` instance of
`gaussianFreeField_satisfies_all_OS_axioms_generic`. -/
theorem gaussianFreeField_satisfies_all_OS_axioms_dim2 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 2 m) :=
  gaussianFreeField_satisfies_all_OS_axioms_generic m

/-- Master theorem, three-dimensional instance: the free GFF with the Yukawa covariance
`e^{-mr}/(4πr)` satisfies all Osterwalder-Schrader axioms. This is the `d = 3` instance of
`gaussianFreeField_satisfies_all_OS_axioms_generic`. -/
theorem gaussianFreeField_satisfies_all_OS_axioms_dim3 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 3 m) :=
  gaussianFreeField_satisfies_all_OS_axioms_generic m

/-- Master theorem, four-dimensional instance: the free GFF with the Bessel
covariance `(m/4π²r) K₁(mr)` satisfies all Osterwalder-Schrader axioms.

This is the `d = 4` instance of
`gaussianFreeField_satisfies_all_OS_axioms_generic`. -/
theorem gaussianFreeField_satisfies_all_OS_axioms_dim4 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 4 m) :=
  gaussianFreeField_satisfies_all_OS_axioms_generic m

/-- Master theorem, five-dimensional instance: the free GFF with the `K_{3/2}` covariance
`(1 + mr) e^{-mr}/(8π²r³)` satisfies all Osterwalder-Schrader axioms. This is the `d = 5` instance
of `gaussianFreeField_satisfies_all_OS_axioms_generic`. -/
theorem gaussianFreeField_satisfies_all_OS_axioms_dim5 (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF 5 m) :=
  gaussianFreeField_satisfies_all_OS_axioms_generic m

end

end OSforGFF
