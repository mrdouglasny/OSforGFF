# Gaussian Measure Construction

Construction of the Gaussian Free Field (GFF) measure on the space of distributional field configurations, verification of its Gaussian property, and proof that it satisfies the Osterwalder-Schrader axioms.

## Mathematical Background

The Gaussian Free Field measure $\mu_{\text{GFF}}$ is the probability measure on the space of tempered distributions $\mathcal{S}'(\mathbb{R}^4)$ characterized by its characteristic functional:

$$\int e^{i\langle\omega,f\rangle}\ d\mu(\omega) = e^{-\frac{1}{2}C(f,f)}$$

where $C(f, g) = \iint f(x)\ C(x-y)\ g(y)\ dx\ dy$ is the free covariance bilinear form with kernel $C(x-y) = \frac{m}{4\pi^2\|x\|}K_1(m\|x\|)$.

The construction uses the **Minlos theorem**: a continuous, positive-definite functional on a nuclear space is the characteristic functional of a unique probability measure on the dual space.

Key properties to verify:
- **Existence:** The characteristic functional $e^{-\frac{1}{2}C(f,f)}$ is positive-definite and continuous.
- **Gaussianity:** $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$, i.e., the generating functional has the Gaussian form.
- **Centered:** The mean vanishes: $\int\langle\omega,f\rangle\ d\mu = 0$.
- **Moments:** $\int\langle\omega,f\rangle^2\ d\mu = C(f,f)$, and all pairings have finite moments of all orders.

## Proof Strategy

### Step 1: Verify Minlos Hypotheses

The Minlos theorem requires three inputs:

1. **Positive definiteness of $e^{-\frac{1}{2}C(f,f)}$:** This follows from the Hilbert space embedding $C(f,f) = \|Tf\|^2$, combined with the abstract result that $e^{-\frac{1}{2}\|h\|^2}$ is positive-definite on any inner product space (proved via the Schur product theorem and Hadamard exponential).

2. **Nuclearity of Schwartz space:** Assumed as an axiom (`schwartz_nuclear`). This is a standard result whose proof requires the Hilbert-Schmidt theory of Schwartz seminorms.

3. **Continuity of $f \mapsto C(f,f)$:** Proved via the continuity of the embedding map $T$ and the fact that $L^2$ norm is continuous.

### Step 2: Construct the Measure

Apply the Minlos theorem to obtain a probability measure $\mu$ on $\text{FieldConfiguration} = \text{WeakDual}\ \mathbb{R}\ \text{TestFunction}$ satisfying the characteristic function identity.

### Step 3: Prove Gaussianity

The real characteristic functional $Z[J] = e^{-\frac{1}{2}C(J,J)}$ for real $J$ is proved directly from the Minlos construction. Extension to complex test functions uses analytic continuation:

1. For real parameters $t, s$ and real test functions $f, g$: $Z(tf + sg) = e^{-\frac{1}{2}(t^2 C(f,f) + 2ts\ C(f,g) + s^2 C(g,g))}$.
2. Both sides are analytic in $(t,s)$ in $\mathbb{C}^2$ (the left side by Fernique's theorem, the right by composition with a polynomial).
3. They agree on $\mathbb{R}^2$, so by analytic continuation they agree on $\mathbb{C}^2$.
4. Any complex test function $J$ can be written as $z_0 f + z_1 g$ for suitable real $f, g$ and complex $z_0, z_1$.

### Step 4: Extract Correlation Functions

From the complex Gaussian identity $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$:
- **2-point function:** Differentiate twice: $S_2(f, g) = C(f, g)$.
- **Centered:** Differentiate once: $\int\langle\omega,f\rangle\ d\mu = 0$.
- **Higher moments:** All determined by Wick's theorem from the 2-point function.

## Key Declarations

### Minlos Theorem (`Minlos.lean`)

| Declaration | Description |
|-------------|-------------|
| [`NuclearSpace`](../OSforGFF/NuclearSpace.lean#L126) | Nuclear space via Hilbert-Schmidt embedding characterization |
| [`schwartz_nuclear`](../OSforGFF/NuclearSpace.lean#L145) | Schwartz space is nuclear (axiom) |
| [`minlos_uniqueness`](../OSforGFF/Minlos.lean#L89) | Derived: two measures with same CF on nuclear space are equal |
| [`gaussian_characteristic_functional`](../OSforGFF/Minlos.lean#L104) | $f \mapsto e^{-\frac{1}{2}C(f,f)}$ |
| [`gaussian_rbf_pd_innerProduct`](../OSforGFF/Minlos.lean#L129) | $e^{-\lVert h\rVert^2/2}$ is positive-definite |
| [`gaussian_positive_definite_via_embedding`](../OSforGFF/Minlos.lean#L141) | $e^{-\frac{1}{2}C(f,f)}$ is positive-definite when $C(f,f) = \lVert Tf\rVert^2$ |
| [`minlos_gaussian_construction`](../OSforGFF/Minlos.lean#L186) | $\exists\ \mu$ with $\int e^{i\langle\omega,f\rangle}\ d\mu = e^{-\frac{1}{2}C(f,f)}$ |
| [`gaussian_measure_characteristic_functional`](../OSforGFF/Minlos.lean#L221) | Same, returning `ProbabilityMeasure` |
| [`gaussian_measure_symmetry`](../OSforGFF/Minlos.lean#L254) | If $g$ preserves $C$, then $g_*\mu = \mu$ |

### Analytic Properties (`MinlosAnalytic.lean`)

| Declaration | Description |
|-------------|-------------|
| [`CovarianceForm`](../OSforGFF/MinlosAnalytic.lean#L52) | Structure packaging a bilinear form $Q$ with its properties |
| [`negMap`](../OSforGFF/MinlosAnalytic.lean#L63) | The negation map $\omega \mapsto -\omega$ |
| [`negMap_measurable`](../OSforGFF/MinlosAnalytic.lean#L66) | Negation is measurable |
| [`integral_neg_invariance`](../OSforGFF/MinlosAnalytic.lean#L75) | $\mu$ is invariant under $\omega \mapsto -\omega$ |
| [`moment_zero_from_realCF`](../OSforGFF/MinlosAnalytic.lean#L196) | $\int\langle\omega,a\rangle\ d\mu = 0$ |

### GFF Construction (`GFFMconstruct.lean`)

| Declaration | Description |
|-------------|-------------|
| [`CovarianceFunction`](../OSforGFF/GFFMconstruct.lean#L124) | Type packaging covariance data for the construction |
| [`isCenteredGJ`](../OSforGFF/GFFMconstruct.lean#L133) | Predicate: $\int\langle\omega,f\rangle\ d\mu = 0$ for all $f$ |
| [`isGaussianGJ`](../OSforGFF/GFFMconstruct.lean#L138) | Predicate: $Z[J] = e^{-\frac{1}{2}S_2(J,J)}$ |
| [`instNuclear_TestFunction`](../OSforGFF/GFFMconstruct.lean#L149) | Instance: `TestFunction` is a `NuclearSpace` |
| [`constructGaussianMeasureMinlos_free`](../OSforGFF/GFFMconstruct.lean#L152) | Minlos construction applied to free covariance |
| [`gaussianFreeField_free`](../OSforGFF/GFFMconstruct.lean#L177) | The GFF probability measure on `FieldConfiguration` |
| `mu_GFF` | Alias for `gaussianFreeField_free` |
| [`gff_real_characteristic`](../OSforGFF/GFFMconstruct.lean#L185) | $Z[J] = e^{-\frac{1}{2}C(J,J)}$ for real $J$ |
| [`gff_pairing_is_gaussian`](../OSforGFF/GFFMconstruct.lean#L272) | Law of $\langle\omega,\phi\rangle$ is $\mathcal{N}(0, C(\phi,\phi))$ |
| [`gaussianFreeField_pairing_memLp`](../OSforGFF/GFFMconstruct.lean#L295) | $\langle\omega,\phi\rangle \in L^p$ for all $p < \infty$ |
| [`gff_pairing_square_integrable`](../OSforGFF/GFFMconstruct.lean#L311) | $\langle\omega,\phi\rangle^2$ is integrable |
| [`gff_second_moment_eq_covariance`](../OSforGFF/GFFMconstruct.lean#L329) | $\int\langle\omega,\phi\rangle^2\ d\mu = C(\phi,\phi)$ |
| [`freeCovarianceFormR_gaussian_cf_pd`](../OSforGFF/GFFMconstruct.lean#L355) | Gaussian CF with free covariance is positive-definite |
| [`freeCovarianceForm`](../OSforGFF/GFFMconstruct.lean#L370) | The `CovarianceForm` structure for the free theory |
| [`gaussianFreeField_free_centered`](../OSforGFF/GFFMconstruct.lean#L387) | $\int\langle\omega,f\rangle\ d\mu = 0$ |
| [`gaussianFreeField_pairing_expSq_integrable`](../OSforGFF/GFFMconstruct.lean#L426) | $e^{\alpha\langle\omega,\phi\rangle^2}$ is integrable for small $\alpha$ |
| [`gaussian_pairing_square_integrable_real`](../OSforGFF/GFFMconstruct.lean#L454) | $\langle\omega,\phi\rangle^2$ integrable (real pairing version) |

### Gaussian Moments (`GaussianMoments.lean`)

| Declaration | Description |
|-------------|-------------|
| [`gaussian_complex_pairing_abs_sq_integrable`](../OSforGFF/GaussianMoments.lean#L55) | $|\langle\omega,\phi\rangle|^2$ is integrable for complex $\phi$ |
| [`gaussian_pairing_product_integrable_free_2point`](../OSforGFF/GaussianMoments.lean#L115) | $\langle\omega,\phi\rangle\langle\omega,\psi\rangle$ is integrable for complex $\phi, \psi$ |
| [`covariance_bilinear_from_general`](../OSforGFF/GaussianMoments.lean#L241) | `CovarianceBilinear` holds for the GFF |

### Gaussian Identity (`GFFIsGaussian.lean`)

| Declaration | Description |
|-------------|-------------|
| [`gff_complex_characteristic_OS0`](../OSforGFF/GFFIsGaussian.lean#L225) | $Z_{\mathbb{C}}[J] = e^{-\frac{1}{2}C_{\text{bilinear}}(J,J)}$ for complex $J$ |
| [`schwinger_eq_covariance_real`](../OSforGFF/GFFIsGaussian.lean#L376) | $S_2(f,g) = C(f,g)$ for real $f, g$ |
| [`gff_two_point_equals_covarianceℂ_free`](../OSforGFF/GFFIsGaussian.lean#L467) | $S_2(f,g) = C(f,g)$ for complex $f, g$ |
| [`gff_complex_generating`](../OSforGFF/GFFIsGaussian.lean#L527) | $Z_{\mathbb{C}}[J] = e^{-\frac{1}{2}S_2(J,J)}$ |
| [`isGaussianGJ_gaussianFreeField_free`](../OSforGFF/GFFIsGaussian.lean#L543) | The GFF satisfies `IsGaussianGJ` |
| [`gff_two_param_analytic`](../OSforGFF/GFFIsGaussian.lean#L100) | $(z_0,z_1) \mapsto Z[z_0 f + z_1 g]$ analytic on $\mathbb{C}^2$ |
| [`gff_slice_analytic_z0`](../OSforGFF/GFFIsGaussian.lean#L127) | $z_0 \mapsto Z[z_0 f + tg]$ is analytic |
| [`gff_slice_analytic_z1`](../OSforGFF/GFFIsGaussian.lean#L155) | $z_1 \mapsto Z[z_0 f + z_1 g]$ is analytic |
| [`gff_cf_agrees_on_reals_OS0`](../OSforGFF/GFFIsGaussian.lean#L209) | Complex $Z$ agrees with real $Z$ on real parameters |

### Master Theorem (`GaussianFreeField.lean`)

| Declaration | Description |
|-------------|-------------|
| [`gaussian_satisfies_OS0`](../OSforGFF/GaussianFreeField.lean#L114) | Gaussian measures satisfy OS0 (analyticity) |
| [`gaussian_satisfies_OS2`](../OSforGFF/GaussianFreeField.lean#L219) | Gaussian measures satisfy OS2 (Euclidean invariance) |
| [`CovarianceContinuous`](../OSforGFF/GaussianFreeField.lean#L82) | Predicate: covariance is jointly continuous |
| [`CovarianceEuclideanInvariant`](../OSforGFF/GaussianFreeField.lean#L208) | Predicate: $C(gx, gy) = C(x,y)$ |
| [`CovarianceEuclideanInvariantℂ`](../OSforGFF/GaussianFreeField.lean#L214) | Complex version |
| [`GJcov_bilin`](../OSforGFF/GaussianFreeField.lean#L97) | Covariance as a `BilinMap` |

## Detailed Proof Outline

### Minlos Construction

1. **Embedding:** From `CovarianceR.lean`, we have `sqrtPropagatorEmbedding`: there exists a Hilbert space $H$ and a linear map $T\colon \text{TestFunction} \to H$ such that $C(f,f) = \|Tf\|^2$.

2. **Positive definiteness:** The function $f \mapsto e^{-\frac{1}{2}\|Tf\|^2}$ is positive-definite because:
   - $e^{-\frac{1}{2}\|h\|^2}$ is positive-definite on $H$ (by `gaussian_rbf_pd_innerProduct`, proved via Schur product theorem and Hadamard exponential series).
   - Composition with a linear map preserves positive definiteness (`gaussian_positive_definite_via_embedding`).

3. **Continuity:** $f \mapsto C(f,f) = \|Tf\|^2$ is continuous because $T = \text{embeddingMapCLM}$ is a continuous linear map, and squaring the norm is continuous.

4. **Application:** `minlos_gaussian_construction` yields $\mu$ with the characteristic functional identity.

### Analytic Continuation to Complex Test Functions

The extension from real to complex characteristic functions (`gff_complex_characteristic_OS0`) is the most technically involved step:

1. **Two real parameters:** For fixed real $f, g$, both sides of the identity are entire functions of $(z_0, z_1) \in \mathbb{C}^2$.
   - Left side: `gff_two_param_analytic` uses the fact that $Z$ is given by an integral of $e^{i\langle\omega, z_0 f + z_1 g\rangle}$, which is analytic by Fernique's theorem (sub-Gaussian integrability).
   - Right side: `gaussian_rhs_slice_analytic_z0/z1` are analytic because they are compositions of exp with a polynomial.

2. **Agreement on reals:** `gff_cf_agrees_on_reals_OS0` shows both sides agree for real $z_0, z_1$, which follows from `gff_real_characteristic`.

3. **Analytic continuation:** Functions analytic on $\mathbb{C}^2$ that agree on $\mathbb{R}^2$ must agree everywhere (by the identity theorem, applied slice by slice).

4. **General complex $J$:** Any $J \in \text{TestFunctionC}$ can be decomposed as $z_0 f + z_1 g$ where $f = \mathrm{Re}(J)$, $g = \mathrm{Im}(J)$, and $z_0 = 1$, $z_1 = i$.

### Extracting the 2-Point Function

From $Z[J] = e^{-\frac{1}{2}C(J,J)}$:

1. **Real case:** Differentiate $\int e^{it\langle\omega,f\rangle} e^{is\langle\omega,g\rangle}\ d\mu$ at $t = s = 0$ twice to get $\int\langle\omega,f\rangle\langle\omega,g\rangle\ d\mu = C(f,g)$. The rigorous argument uses the explicit Gaussian formula for the second moment.

2. **Complex extension:** `gff_two_point_equals_covarianceℂ_free` extends to complex test functions by expressing complex test functions as linear combinations of real ones and using bilinearity.

### Integrability of Moments

The proof that $\langle\omega,\phi\rangle\langle\omega,\psi\rangle$ is integrable (`gaussian_pairing_product_integrable_free_2point`) uses:

1. `gaussianFreeField_pairing_expSq_integrable`: there exists $\alpha > 0$ such that $e^{\alpha\langle\omega,\phi\rangle^2}$ is integrable. This follows from the Fernique theorem applied to the Gaussian distribution of $\langle\omega,\phi\rangle$.

2. From exp-square integrability, derive $L^p$ membership for all $p < \infty$ via Holder's inequality.

3. Apply Cauchy-Schwarz: $|\langle\omega,\phi\rangle\langle\omega,\psi\rangle| \le \tfrac{1}{2}(|\langle\omega,\phi\rangle|^2 + |\langle\omega,\psi\rangle|^2)$, so integrability of squares implies integrability of products.

## References

- Minlos, R. A. "Generalized random processes and their extension to a measure", *Trudy Moskov. Mat. Obsc.* 8 (1959), 497-518.
- Glimm, J. and Jaffe, A. *Quantum Physics: A Functional Integral Point of View*, Ch. 6.
- Simon, B. *The $P(\phi)_2$ Euclidean (Quantum) Field Theory*, Ch. I.
- Fernique, X. "Regularite des trajectoires des fonctions aleatoires gaussiennes", *Ecole d'Ete de Probabilites de Saint-Flour* IV (1974).
- Bogachev, V. I. *Gaussian Measures*, AMS Mathematical Surveys and Monographs (1998).
