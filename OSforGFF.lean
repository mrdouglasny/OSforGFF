/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
-- Root import file for the OSforGFF library.

-- General mathematics (pure Mathlib extensions, no project imports)
import «OSforGFF».General.FunctionalAnalysis
import «OSforGFF».General.FrobeniusPositivity
import «OSforGFF».General.SchurProduct
import «OSforGFF».General.HadamardExp
import «OSforGFF».General.PositiveDefinite
import «OSforGFF».General.GaussianRBF
import «OSforGFF».General.FourierTransforms
import «OSforGFF».General.LaplaceIntegral
import «OSforGFF».General.BesselFunction
import «OSforGFF».General.QuantitativeDecay
import «OSforGFF».General.SchwartzTranslationDecay
import «OSforGFF».General.L2TimeIntegral

-- Spacetime (test functions & symmetries)
import «OSforGFF».Spacetime.Basic
import «OSforGFF».Spacetime.Euclidean
import «OSforGFF».Spacetime.DiscreteSymmetry
import «OSforGFF».Spacetime.Decomposition
import «OSforGFF».Spacetime.ComplexTestFunction
import «OSforGFF».Spacetime.PositiveTimeTestFunction
import «OSforGFF».Spacetime.TimeTranslation
import «OSforGFF».Spacetime.ProdIntegrable
import «OSforGFF».Spacetime.Tonelli

-- Schwinger (generating functionals)
import «OSforGFF».Schwinger.Defs
import «OSforGFF».Schwinger.TwoPoint
import «OSforGFF».Schwinger.GaussianMoments

-- Covariance (free propagator)
import «OSforGFF».Covariance.Momentum
import «OSforGFF».Covariance.Position
import «OSforGFF».Covariance.RealForm
import «OSforGFF».Covariance.Parseval

-- Measure (Minlos + GFF construction)
import «OSforGFF».Measure.NuclearSpace
import «OSforGFF».Measure.Minlos
import «OSforGFF».Measure.MinlosAnalytic
import «OSforGFF».Measure.Construct
import «OSforGFF».Measure.IsGaussian
import «OSforGFF».Measure.GaussianFreeField

-- OS axioms (definitions + proofs)
import «OSforGFF».OS.Axioms
import «OSforGFF».OS.OS0_Analyticity
import «OSforGFF».OS.OS1_Regularity
import «OSforGFF».OS.OS2_Invariance
import «OSforGFF».OS.OS3_MixedRepInfra
import «OSforGFF».OS.OS3_MixedRep
import «OSforGFF».OS.OS3_CovarianceRP
import «OSforGFF».OS.OS3_ReflectionPositivity
import «OSforGFF».OS.OS4_MGF
import «OSforGFF».OS.OS4_Clustering
import «OSforGFF».OS.OS4_Ergodicity

-- Master theorem
import «OSforGFF».OS.Master
