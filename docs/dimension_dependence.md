# Dimension Dependence

This document inventories where the spacetime dimension $d = 4$ (and spatial dimension $d-1 = 3$) enters the proofs. The project defines `STDimension := 4` in `Spacetime/Basic.lean`  changing this value would require updates to every file listed below as **essential** or **spatial**.

## Classification

- **Essential (d=4):** The mathematical formula is specific to $d = 4$. Generalizing requires deriving the analogous formula in dimension $d$.
- **Spatial (d=3):** Uses the spatial dimension $d - 1 = 3$ explicitly, typically for integrability estimates.
- **Structural:** References `STDimension` or `SpaceTime` but the proof works for any $d$ without change (beyond updating the abbreviation).

## Essential (d=4)

These files contain formulas that evaluate differently in other dimensions.

### `Covariance/Momentum.lean`
- **Heat kernel normalization:** `heatKernelPositionSpace` uses $(4\pi t)^{-d/2}$, which evaluates to $1/(16\pi^2 t^2)$ for $d=4$.
- **Bessel representation:** `freeCovarianceBessel` gives $C(x,y) = \frac{m}{4\pi^2 r} K_1(mr)$, the closed-form specific to $d=4$.
- **Schwinger evaluation:** `covarianceSchwingerRep_eq_besselFormula` connects the proper-time integral to the Bessel form.
- **Regulated convergence:** `freeCovariance_regulated_tendsto_bessel` and domination bounds use the $d=4$ Bessel form.

### `Covariance/Parseval.lean`
- **Plancherel scaling:** The factor $(2\pi)^d$ appears in `regulated_fubini_factorization`, `parseval_covariance_schwartz_regulated`, and the change-of-variables between physics and Mathlib Fourier conventions.

### `OS/OS3_MixedRepInfra.lean`
- **Heat kernel 4D expansion:** `heatKernelPositionSpace_4D` converts $(4\pi t)^{-d/2}$ to $1/(16\pi^2 t^2)$.
- **Schwinger proper-time integral:** Uses the $d=4$ heat kernel in the Laplace $s$-integral.

### `OS/OS3_MixedRep.lean`
- **Normalization identity:** Uses $(2\pi)^4 / (2\pi) = (2\pi)^3$ to factor the mixed representation.
- **Schwinger-to-Bessel reduction:** Dimension-specific simplifications throughout.

### `General/BesselFunction.lean`
- **$K_1$ definition and bounds:** The modified Bessel function $K_1$ is the kernel that appears in $d=4$. In general dimension $d$, the covariance involves $K_{d/2-1}$.

## Spatial (d=3)

These files use the spatial dimension $d-1 = 3$ for integrability.

### `General/FunctionalAnalysis.lean`
- **`polynomial_decay_integrable_3d`:** $(1+\|x\|)^{-4}$ is integrable in $\mathbb{R}^3$ because the decay rate $4 > d-1 = 3$. In general dimension, the required decay rate would be $> d-1$.

### `Spacetime/ProdIntegrable.lean`
- **`SpatialCoords3`:** Defined as `EuclideanSpace ℝ (Fin 3)`. Spatial marginal integrals use this type.
- **Spatial marginal bounds:** The linear vanishing bound `spatialNormIntegral_linear_bound` uses 3D spatial integrals.

### `OS/OS1_Regularity.lean`
- **Local integrability:** Uses `locallyIntegrable_of_rpow_decay_real` with $\alpha = 2 < d = 4$ and $d \ge 3$. In general dimension $d$, the singularity is $\|x\|^{-(d-2)}$, so the condition becomes $d-2 < d$, which always holds.

### `OS/OS4_Clustering.lean`
- **Norm decomposition:** `Fin.sum_univ_four` expands $\|k\|^2 = k_0^2 + k_1^2 + k_2^2 + k_3^2$, coupling to $d=4$.

## Structural (dimension-agnostic)

These files reference `STDimension` or `SpaceTime` but work for any $d \ge 2$.

| File | Usage |
|------|-------|
| `Spacetime/Basic.lean` | Defines `STDimension`, `SpaceTime`, `getTimeComponent`, `SpatialCoords`, `spatialPart`, `E` |
| `OS/Axioms.lean` | OS axiom definitions (quantify over test functions on `SpaceTime`) |
| `Spacetime/Euclidean.lean` | Euclidean group $E(d) = O(d) \rtimes \mathbb{R}^d$ |
| `Spacetime/DiscreteSymmetry.lean` | Time reflection matrix in $O(d)$ |
| `Spacetime/TimeTranslation.lean` | Time translation $T_s$ (shift index 0) |
| `Spacetime/Decomposition.lean` | Decomposition $\mathbb{R}^d \cong \mathbb{R} \times \mathbb{R}^{d-1}$ |
| `Spacetime/ComplexTestFunction.lean` | Complex test function operations |
| `Spacetime/PositiveTimeTestFunction.lean` | Positive-time support predicate |
| `Schwinger/Defs.lean` | Schwinger $n$-point functions |
| `Schwinger/TwoPoint.lean` | Distributional 2-point function |
| `Covariance/Position.lean` | Bilinear covariance form (uses Parseval, so inherits d=4) |
| `Covariance/RealForm.lean` | Real covariance, Hilbert space embedding |
| `Measure/GaussianFreeField.lean` | GFF measure construction via Minlos |
| `Measure/Construct.lean` | Measure construction infrastructure |
| `Measure/IsGaussian.lean` | Gaussianity verification |
| `Schwinger/GaussianMoments.lean` | Moment computations |
| `Measure/Minlos.lean` | Minlos theorem (axiom, dimension-independent) |
| `Measure/MinlosAnalytic.lean` | Analytic continuation of characteristic functional |
| `OS/OS0_Analyticity.lean` | OS0 proof (analyticity) |
| `OS/OS2_Invariance.lean` | OS2 proof (Euclidean invariance) |
| `OS/OS3_CovarianceRP.lean` | Covariance RP (uses mixed rep, inherits d=4) |
| `OS/OS3_ReflectionPositivity.lean` | OS3 assembly (includes RP bridge to real formulation) |
| `OS/OS4_MGF.lean` | MGF infrastructure for OS4 |
| `OS/OS4_Ergodicity.lean` | Ergodicity from polynomial clustering |
| `General/L2TimeIntegral.lean` | $L^2$ time integral estimates |
| `OS/Master.lean` | Master theorem assembly |
| `General/FourierTransforms.lean` | 1D Fourier transform identities |
| `General/LaplaceIntegral.lean` | Laplace/Glasser integrals |
| `General/HadamardExp.lean` | Hadamard exponential |
| `General/SchurProduct.lean` | Schur product theorem |
| `General/FrobeniusPositivity.lean` | Frobenius inner product positivity |
| `General/PositiveDefinite.lean` | Positive-definite function theory |
| `General/GaussianRBF.lean` | Gaussian RBF positive definiteness |
| `General/QuantitativeDecay.lean` | Polynomial decay estimates |
| `General/SchwartzTranslationDecay.lean` | Bilinear translation decay |
| `Spacetime/Tonelli.lean` | Tonelli for spacetime integrals |

## Generalization Notes

To port the project to a different dimension $d$:
1. Change `STDimension` in `Spacetime/Basic.lean`.
2. Replace the Bessel $K_1$ representation with the general $K_{d/2-1}$ form.
3. Update the heat kernel normalization $(4\pi t)^{-d/2}$.
4. Update Plancherel scaling factors $(2\pi)^d$.
5. Verify spatial integrability: decay rate must exceed $d-1$.
6. Replace `Fin.sum_univ_four` with the appropriate `Fin.sum_univ` variant.
