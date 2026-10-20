/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
-- Root import file for the OSforGFF library.

-- General mathematics (pure Mathlib extensions, no project imports)
module

public import «OSforGFF».General.FunctionalAnalysis
public import «OSforGFF».General.SchurProduct
public import «OSforGFF».General.HadamardExp
public import «OSforGFF».General.PositiveDefinite
public import «OSforGFF».General.GaussianRBF
public import «OSforGFF».General.FourierTransforms
public import «OSforGFF».General.LaplaceIntegral
public import «OSforGFF».General.BesselFunction
public import «OSforGFF».General.BesselK0
public import «OSforGFF».General.BesselK
public import «OSforGFF».General.QuantitativeDecay
public import «OSforGFF».General.SchwartzTranslationDecay
public import «OSforGFF».General.L2TimeIntegral

-- Spacetime (test functions & symmetries)
public import «OSforGFF».Spacetime.Basic
public import «OSforGFF».Spacetime.Euclidean
public import «OSforGFF».Spacetime.DiscreteSymmetry
public import «OSforGFF».Spacetime.Decomposition
public import «OSforGFF».Spacetime.ComplexTestFunction
public import «OSforGFF».Spacetime.PositiveTimeTestFunction
public import «OSforGFF».Spacetime.TimeTranslation
public import «OSforGFF».Spacetime.ProdIntegrable
public import «OSforGFF».Spacetime.Tonelli

-- Schwinger (generating functionals)
public import «OSforGFF».Schwinger.Defs
public import «OSforGFF».Schwinger.TwoPoint
public import «OSforGFF».Schwinger.GaussianMoments

-- Covariance (free propagator)
public import «OSforGFF».Covariance.Propagator
public import «OSforGFF».Covariance.ParsevalGeneric

-- Instances (per-dimension propagator closed forms)
public import «OSforGFF».Instances.Dim4
public import «OSforGFF».Instances.Dim3
public import «OSforGFF».Instances.Dim2
public import «OSforGFF».Instances.Dim5

public import «OSforGFF».Covariance.RealForm

-- Measure (Minlos + GFF construction)
public import «OSforGFF».Measure.NuclearSpace
public import «OSforGFF».Measure.WeakDualMeasurableSpace
public import «OSforGFF».Measure.Minlos
public import «OSforGFF».Measure.MinlosAnalytic
public import «OSforGFF».Measure.Construct
public import «OSforGFF».Measure.IsGaussian
public import «OSforGFF».Measure.GaussianFreeField

-- OS axioms (definitions + proofs)
public import «OSforGFF».OS.Axioms
public import «OSforGFF».OS.OS0_Analyticity
public import «OSforGFF».OS.OS1_Regularity
public import «OSforGFF».OS.OS2_Invariance
public import «OSforGFF».OS.OS3_MixedRepInfra
public import «OSforGFF».OS.OS3_MixedRep
public import «OSforGFF».OS.OS3_CovarianceRP
public import «OSforGFF».OS.OS3_ReflectionPositivity
public import «OSforGFF».OS.OS4_MGF
public import «OSforGFF».OS.OS4_Clustering
public import «OSforGFF».OS.OS4_Ergodicity

-- Master theorem
public import «OSforGFF».OS.Master

-- Build-enforced guardrails (axiom-footprint + statement-type). See OSforGFF/Guardrails.lean.
public import «OSforGFF».Guardrails
