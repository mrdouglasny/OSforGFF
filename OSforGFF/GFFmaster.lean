/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
/-
Final bundling of OS axioms for the free Gaussian Free Field (GFF).

This file provides a "master theorem" that assembles OS0–OS4 for the
measure `gaussianFreeField_free m`, reusing the individual results proved
elsewhere:
- OS0 is proved in `OSforGFF/OS0_GFF.lean` via the holomorphic integral theorem
  (differentiation under the integral sign)
- OS1 is proved in `OSforGFF/OS1_GFF.lean` via Fourier/momentum space methods
- OS2 is proved in `OSforGFF/OS2_GFF.lean` via Euclidean invariance of the free covariance
- OS3 is proved in `OSforGFF/OS3_GFF.lean` via the matrix/Schur–Hadamard argument
- OS4 Clustering is proved in `OSforGFF/OS4_Clustering.lean` via Gaussian factorization and decay
- OS4 Ergodicity is proved in `OSforGFF/OS4_Ergodicity.lean` via polynomial clustering → ergodicity

We expose an unconditional master theorem: all five OS axioms hold for the free GFF.
-/

import OSforGFF.GaussianFreeField
import OSforGFF.OS3_GFF
import OSforGFF.OS0_GFF
import OSforGFF.OS1_GFF
import OSforGFF.OS2_GFF
import OSforGFF.OS4_Clustering
import OSforGFF.OS4_Ergodicity

open scoped BigOperators

namespace OSforGFF

noncomputable section

/-! ## Master OS theorem for the free GFF -/

/-- Master theorem: the free GFF satisfies all Osterwalder-Schrader axioms.
- OS0 is supplied by `QFT.gaussianFreeField_satisfies_OS0` via the holomorphic integral theorem
- OS1 is supplied by `gaussianFreeField_satisfies_OS1_revised` via Fourier/momentum space methods
- OS2 is supplied by `gaussian_satisfies_OS2` via Euclidean invariance of the free covariance
- OS3 is supplied by `QFT.gaussianFreeField_OS3_real` via the Schur-Hadamard argument
- OS4 Clustering is supplied by `QFT.gaussianFreeField_satisfies_OS4` via Gaussian factorization
- OS4 Ergodicity is supplied by polynomial clustering (α=6) → ergodicity

This is an unconditional theorem with no assumptions beyond m > 0. -/
theorem gaussianFreeField_satisfies_all_OS_axioms (m : ℝ) [Fact (0 < m)] :
    SatisfiesAllOS (μ_GFF m) where
  -- OS0 from the holomorphic integral theorem (differentiation under the integral)
  os0 := QFT.gaussianFreeField_satisfies_OS0 m
  -- OS1 from the free field theorem using Fourier/momentum space methods
  os1 := gaussianFreeField_satisfies_OS1_revised m
  -- OS2 from Euclidean invariance of free covariance
  os2 := gaussian_satisfies_OS2 (μ_GFF m)
    (by exact isGaussianGJ_gaussianFreeField_free m)
    (QFT.CovarianceEuclideanInvariantℂ_μ_GFF m)
  -- OS3 from the Schur-Hadamard argument
  os3 := QFT.gaussianFreeField_OS3_real m
  -- OS4 Clustering (Gaussian factorization and covariance decay)
  os4_clustering := QFT.gaussianFreeField_satisfies_OS4 m
  -- OS4 Ergodicity: polynomial clustering (α=6) implies ergodicity
  os4_ergodicity := OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity m
    (QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering m 6 (by norm_num))

end

end OSforGFF
