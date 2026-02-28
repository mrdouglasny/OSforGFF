# Master Theorem: GFF Satisfies All OS Axioms

## Mathematical Background

The master theorem assembles the individual axiom proofs into a single statement: the Gaussian Free Field with mass $m > 0$ in 4-dimensional Euclidean spacetime satisfies all Osterwalder-Schrader axioms. This is the culmination of the formalization, establishing that the free scalar field defines a consistent Euclidean QFT that can be analytically continued to a physical relativistic quantum field theory via the OS reconstruction theorem.

### Statement

For any mass parameter $m > 0$, the GFF probability measure $\mu_{\mathrm{GFF}}(m)$ satisfies:

- **OS0** (Analyticity): The generating functional is analytic in the test functions.
- **OS1** (Regularity): The generating functional satisfies exponential bounds.
- **OS2** (Euclidean Invariance): The measure is invariant under 4D Euclidean transformations.
- **OS3** (Reflection Positivity): The quadratic form $\sum_{ij} c_i c_j\  \mathrm{Re}\left(Z[f_i - \Theta f_j]\right) \geq 0$.
- **OS4** (Clustering): Distant test functions become statistically independent.
- **OS4** (Ergodicity): Time averages of generating-function observables converge to ensemble averages.

## Key Declarations

| Declaration | File | Description |
|-------------|------|-------------|
| [`gaussianFreeField_satisfies_all_OS_axioms`](../OSforGFF/OS/Master.lean#L48) | `OS/Master.lean` | **Master theorem**: conjunction of all OS axioms |
| [`QFT.gaussianFreeField_satisfies_OS0`](../OSforGFF/OS/OS0_Analyticity.lean#L1120) | `OS/OS0_Analyticity.lean` | OS0: $z \mapsto Z[\sum z_i J_i]$ analytic |
| [`gaussianFreeField_satisfies_OS1_revised`](../OSforGFF/OS/OS1_Regularity.lean#L528) | `OS/OS1_Regularity.lean` | OS1: $\lvert Z[f]\rvert \le e^{c\lVert f\rVert_2^2}$ |
| [`gaussian_satisfies_OS2`](../OSforGFF/Measure/GaussianFreeField.lean#L219) | `Measure/GaussianFreeField.lean` | OS2: $Z[g\cdot f] = Z[f]$ for $g \in E(4)$ |
| [`QFT.gaussianFreeField_OS3_real`](../OSforGFF/OS/OS3_ReflectionPositivity.lean#L509) | `OS/OS3_ReflectionPositivity.lean` | OS3: $\sum c_ic_j\ \mathrm{Re}\left(Z[f_i-\Theta f_j]\right) \ge 0$ |
| [`QFT.gaussianFreeField_satisfies_OS4`](../OSforGFF/OS/OS4_Clustering.lean#L475) | `OS/OS4_Clustering.lean` | OS4: $Z[f+T_ag] \to Z[f]Z[g]$ as $\lVert a\rVert\to\infty$ |
| [`OS4_PolynomialClustering_implies_OS4_Ergodicity`](../OSforGFF/OS/OS4_Ergodicity.lean#L1339) | `OS/OS4_Ergodicity.lean` | OS4 Ergodicity: $\frac{1}{T}\int_0^T A(T_s\phi)\ ds \xrightarrow{L^2} \mathbb{E}[A]$ |

## How Each Axiom Feeds In

The master theorem in `OS/Master.lean` is a short assembly file (~80 lines) that imports and combines six independently proved results:

```
OS/Master.lean
  |
  +-- OS0: QFT.gaussianFreeField_satisfies_OS0 m
  |     Source: OS/OS0_Analyticity.lean
  |     Technique: Holomorphic integral theorem (differentiation under integral sign)
  |
  +-- OS1: gaussianFreeField_satisfies_OS1_revised m
  |     Source: OS/OS1_Regularity.lean
  |     Technique: Fourier/momentum space bounds on the generating functional
  |
  +-- OS2: gaussian_satisfies_OS2 (mu_GFF m) h_gauss h_euc
  |     Sources: Measure/GaussianFreeField.lean, OS/OS2_Invariance.lean
  |     Technique: Covariance kernel depends only on |x-y|, which is Euclidean-invariant
  |                Gaussianity ensures the full measure inherits this invariance
  |
  +-- OS3: QFT.gaussianFreeField_OS3_real m
  |     Sources: OS/OS3_ReflectionPositivity.lean <- OS/OS3_CovarianceRP.lean
  |              <- OS/OS3_MixedRep.lean <- OS/OS3_MixedRepInfra.lean, General/HadamardExp.lean
  |     Technique: Covariance RP (momentum factorization into |F_omega|^2)
  |                + Hadamard exponential theorem for matrix assembly
  |
  +-- OS4 Clustering: QFT.gaussianFreeField_satisfies_OS4 m
  |     Source: OS/OS4_Clustering.lean
  |     Technique: Gaussian factorization Z[f+g] = Z[f]Z[g]exp(-S_2(f,g))
  |                + cross-covariance decay from propagator decay
  |
  +-- OS4 Ergodicity: OS4_PolynomialClustering_implies_OS4_Ergodicity m h_poly_cluster
        Sources: OS/OS4_Ergodicity.lean, OS/OS4_Clustering.lean
        Technique: Polynomial clustering (alpha=6)
                   -> variance of time average bounded by O(1/T)
                   -> L2 convergence of time averages
```

## Assumed Axioms

The master theorem depends on 3 axioms declared with the `axiom` keyword in Lean. These are standard mathematical results whose full Lean formalization was deferred.

| Axiom | File | Mathematical Content |
|-------|------|---------------------|
| [`minlos_theorem`](../OSforGFF/Measure/Minlos.lean#L77) | `Measure/Minlos.lean` | Continuous positive-definite normalized functional on nuclear space $\implies$ characteristic functional of a unique probability measure ($\exists!$) |
| [`differentiable_analyticAt_finDim`](../OSforGFF/OS/OS0_Analyticity.lean#L86) | `OS/OS0_Analyticity.lean` | Hartogs' theorem: $f : \mathbb{C}^n \supset U \to \mathbb{C}$ differentiable $\implies$ $f$ analytic |
| [`schwartz_nuclear`](../OSforGFF/Measure/NuclearSpace.lean#L145) | `Measure/NuclearSpace.lean` | $\mathcal{S}(\mathbb{R}^n, F)$ is a nuclear TVS |

All three axioms are well-established theorems in functional analysis. The Minlos theorem (existence and uniqueness of measures from characteristic functionals on nuclear spaces) is foundational for infinite-dimensional measure theory. Hartogs' theorem is a standard result in several complex variables. Nuclearity of Schwartz space is proved in standard references on topological vector spaces.

## References

- R.A. Minlos, "Generalized random processes and their extension to a measure," *Trudy Moskov. Mat. Obshch.* 8 (1959), 497--518.
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's Functions I, II," *Comm. Math. Phys.* 31 (1973)  42 (1975).
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer, 1987.
- F. Treves, *Topological Vector Spaces, Distributions and Kernels*, Academic Press, 1967, Chapter 51 (nuclearity of Schwartz space).
