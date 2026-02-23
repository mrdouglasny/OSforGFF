/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
-- This module serves as the root of the `Aqft2` library.
-- Import modules here that should be built as part of the library.

-- Core infrastructure
import «OSforGFF».FunctionalAnalysis
import «OSforGFF».Basic
import «OSforGFF».QuantitativeDecay
import «OSforGFF».ComplexTestFunction
import «OSforGFF».SpacetimeDecomp
import «OSforGFF».TimeTranslation

-- Euclidean group and symmetries
import «OSforGFF».Euclidean
import «OSforGFF».DiscreteSymmetry

-- Fourier analysis
import «OSforGFF».FourierTransforms
import «OSforGFF».Parseval
import «OSforGFF».BesselFunction
import «OSforGFF».LaplaceIntegral

-- Covariance theory
import «OSforGFF».CovarianceMomentum
import «OSforGFF».Covariance
import «OSforGFF».CovarianceR
import «OSforGFF».GaussianRBF
import «OSforGFF».PositiveDefinite

-- Reflection positivity
import «OSforGFF».PositiveTimeTestFunction_real
import «OSforGFF».FrobeniusPositivity
import «OSforGFF».SchurProduct
import «OSforGFF».HadamardExp

-- Schwinger functions
import «OSforGFF».Schwinger
import «OSforGFF».SchwingerTwoPointFunction

-- Measure construction (Minlos)
import «OSforGFF».Minlos
import «OSforGFF».MinlosAnalytic
import «OSforGFF».NuclearSpace.Schwartz
import «OSforGFF».NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion

-- GFF construction
import «OSforGFF».GFFMconstruct
import «OSforGFF».GaussianMoments
import «OSforGFF».GFFIsGaussian
import «OSforGFF».GaussianFreeField

-- Integrability and analysis
import «OSforGFF».L2TimeIntegral
import «OSforGFF».SchwartzTonelli
import «OSforGFF».SchwartzTranslationDecay
import «OSforGFF».SchwartzProdIntegrable

-- OS Axioms
import «OSforGFF».OS_Axioms
import «OSforGFF».OS0_GFF
import «OSforGFF».OS1_GFF
import «OSforGFF».OS2_GFF
import «OSforGFF».OS3_MixedRep
import «OSforGFF».OS3_MixedRepInfra
import «OSforGFF».OS3_CovarianceRP
import «OSforGFF».OS3_GFF
import «OSforGFF».OS4_MGF
import «OSforGFF».OS4_Clustering
import «OSforGFF».OS4_Ergodicity

-- Master theorem
import «OSforGFF».GFFmaster
import «OSforGFF».GFFmasterProved
