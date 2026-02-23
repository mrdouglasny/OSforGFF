# OS0 Analyticity

## Mathematical Background

OS0 (Analyticity) is the first Osterwalder-Schrader axiom. It states that the generating functional $Z[f]$ depends analytically on the test function arguments. This is essential because:

1. **Wick rotation**: Analytic continuation connects Euclidean and Minkowski signatures.
2. **Correlation functions**: Derivatives of $Z$ yield Schwinger $n$-point functions  analyticity ensures these are well-defined.
3. **Perturbation theory**: Taylor expansions of $Z$ give perturbative corrections.

**Theorem (OS0).** For any finite collection of complex test functions $J_1, \ldots, J_n \in \mathcal{S}(\mathbb{R}^4, \mathbb{C})$, the map

$$z = (z_1, \ldots, z_n) \mapsto Z\left[\sum_{i=1}^n z_i J_i\right] = \int_\Omega \exp\left(i \sum_{i=1}^n z_i \langle \omega, J_i \rangle\right) d\mu(\omega)$$

is analytic on $\mathbb{C}^n$.

For the GFF, $\mu = \mu_{\mathrm{GFF}}$ is the Gaussian measure with covariance $C = (-\Delta + m^2)^{-1}$, and the generating functional has the closed form $Z[f] = \exp(-\tfrac{1}{2}\langle f, Cf \rangle)$.

**Lean formalization note.** In the Lean development, `OS0_Analyticity` is stated as **complex Fréchet differentiability** (`Differentiable ℂ`) in finite-dimensional complex directions (see `OSforGFF/OS_Axioms.lean`). Classically, for finite-dimensional complex vector spaces, holomorphy implies analyticity, so this formulation is faithful while avoiding any missing multi-variable SCV “holomorphic ⇒ analytic” library.

## Proof Strategy

The proof applies a **holomorphic (differentiability) under the integral sign theorem**: if the integrand

$$f(z, \omega) = \exp(i\sum_i z_i \langle\omega, J_i\rangle)$$

satisfies appropriate measurability, pointwise analyticity, integrability, and local integrable derivative bounds, then the parametric integral

$$F(z) = \int f(z,\omega)\ d\mu(\omega)$$

is complex Fréchet differentiable on $\mathbb{C}^n$ (in Lean: `Differentiable ℂ F`). This is exactly the OS0 predicate used by the project.

The five hypotheses verified are:
1. Measurability of $\omega \mapsto f(z, \omega)$ for each $z$
2. Analyticity of $z \mapsto f(z, \omega)$ for each $\omega$ (linear + exp composition)
3. Integrability of $f(z, \cdot)$ for each $z$ (Fernique's theorem)
4. Measurability of $\omega \mapsto D_z f(z, \omega)$
5. Local integrable bounds on the Frechet derivative (Holder + Gaussian moments)

**Literature**: Glimm-Jaffe Ch. 6  Hormander, "Complex Analysis in Several Variables".

## Key Declarations

| Declaration | Description |
|-------------|-------------|
| [`gaussianFreeField_satisfies_OS0`](../OSforGFF/OS0_GFF.lean#L1120) | Main theorem: the GFF satisfies OS0 analyticity |
| [`differentiable_integral_of_locally_L1_bound`](../OSforGFF/OS0_GFF.lean#L98) | Analytic integrand + local $L^1$ bounds on the Fréchet derivative $\Rightarrow$ differentiable parametric integral |
| [`gff_integrand_measurable`](../OSforGFF/OS0_GFF.lean#L167) | $\omega \mapsto \exp(i\langle\omega, \sum z_i J_i\rangle)$ is measurable |
| [`gff_integrand_analytic`](../OSforGFF/OS0_GFF.lean#L195) | $z \mapsto \exp(i\langle\omega, \sum z_i J_i\rangle)$ is analytic for fixed $\omega$ |
| [`gff_integrand_integrable`](../OSforGFF/OS0_GFF.lean#L536) | $\exp(i\langle\omega, \sum z_i J_i\rangle) \in L^1(\mu_{\mathrm{GFF}})$ |
| [`gff_integrand_fderiv_measurable`](../OSforGFF/OS0_GFF.lean#L562) | $\omega \mapsto D_z \exp(i\langle\omega, \sum z_i J_i\rangle)$ is measurable |
| [`gff_integrand_fderiv_bound`](../OSforGFF/OS0_GFF.lean#L681) | Local $L^1$ bound on the Frechet derivative |
| [`norm_exp_I_distributionPairingℂ_real`](../OSforGFF/OS0_GFF.lean#L269) | $\lvert e^{i\langle\omega,f\rangle}\rvert = e^{-\omega(f_{\mathrm{im}})}$ |
| [`gff_exp_abs_pairing_integrable`](../OSforGFF/OS0_GFF.lean#L461) | $\exp\lvert\omega(f)\rvert \in L^1(\mu_{\mathrm{GFF}})$ |
| [`gff_exp_abs_pairing_memLp`](../OSforGFF/OS0_GFF.lean#L328) | $\exp\lvert\omega(f)\rvert \in L^p(\mu_{\mathrm{GFF}})$ for $p < \infty$ |
| [`gff_exp_abs_sum_memLp`](../OSforGFF/OS0_GFF.lean#L469) | $\exp(\sum_i |\omega(g_i)|) \in L^2(\mu_{\mathrm{GFF}})$ |
| [`gff_integrand_norm_integrable`](../OSforGFF/OS0_GFF.lean#L522) | $\lvert\exp(i\langle\omega,f\rangle)\rvert \in L^1(\mu_{\mathrm{GFF}})$ |
| [`distributionPairingℂ_real_continuous`](../OSforGFF/OS0_GFF.lean#L152) | $\omega \mapsto \langle\omega, f\rangle$ is continuous |

## Detailed Proof Outline

### Step 1: Analyticity of the integrand in $z$

For fixed $\omega \in \mathcal{S}'$, the function $z \mapsto \exp(i \sum_i z_i \langle\omega, J_i\rangle)$ is entire because:
- The sum $\sum_i z_i \langle\omega, J_i\rangle$ is a linear function of $z$ (hence analytic).
- Multiplication by $i$ and the exponential are entire.
- Composition of analytic functions is analytic.

The key identity is `pairing_linear_combo` from `ComplexTestFunction.lean`, which establishes linearity of the distributional pairing in the test function argument.

**Lean theorem**: `gff_integrand_analytic`

### Step 2: Measurability in $\omega$

For fixed $z$, the map $\omega \mapsto \exp(i\langle\omega, \sum_i z_i J_i\rangle)$ is measurable because the evaluation functional $\omega \mapsto \langle\omega, f\rangle$ is continuous on the weak-* dual $\mathcal{S}'$ (`distributionPairingℂ_real_continuous`), and compositions of continuous functions with measurable operations preserve measurability.

**Lean theorem**: `gff_integrand_measurable`

### Step 3: Integrability

For complex test functions $f = f_{\mathrm{re}} + i f_{\mathrm{im}}$, the norm of the integrand is:

$$\|\exp(i\langle\omega, f\rangle)\| = \exp(-\omega(f_{\mathrm{im}}))$$

This follows from $|e^{a+ib}| = e^a$ applied to $i\langle\omega, f\rangle = i\langle\omega, f_{\mathrm{re}}\rangle - \langle\omega, f_{\mathrm{im}}\rangle$.

When $f_{\mathrm{im}} \ne 0$, the norm $\exp(-\omega(f_{\mathrm{im}}))$ can be large for field configurations where $\omega(f_{\mathrm{im}}) < 0$. Integrability then requires **Fernique's theorem**: for Gaussian measures, $\exp(\alpha \langle\omega, g\rangle^2)$ is integrable for sufficiently small $\alpha > 0$. This is established by `gaussianFreeField_pairing_expSq_integrable` in `GFFMconstruct.lean`.

**Lean theorem**: `gff_integrand_integrable`

### Step 4: Frechet derivative measurability

The Frechet derivative has the explicit form:

$$D_z[\exp(i\langle\omega, \textstyle\sum_i z_i J_i\rangle)] = \exp(i\langle\omega, \textstyle\sum_i z_i J_i\rangle) \cdot i \cdot \sum_i \langle\omega, J_i\rangle \cdot \mathrm{proj}_i$$

This is continuous in $\omega$ as a composition of continuous functions, hence measurable.

**Lean theorem**: `gff_integrand_fderiv_measurable`

### Step 5: Local integrable bound on the derivative

The derivative norm is bounded by:

$$\|D_z f(z, \omega)\| \le \sum_j |\langle\omega, J_j\rangle| \cdot \exp(-\omega(f_{\mathrm{im}}))$$

An integrable dominating function is constructed as:

$$\mathrm{bound}(\omega) = \exp\left(|\omega(f_{\mathrm{im}}^{z_0})| + \sum_i (|\omega(J_{i,\mathrm{re}})| + |\omega(J_{i,\mathrm{im}})|)\right) \cdot \left(1 + \sum_i \|\langle\omega, J_i\rangle\|\right)$$

Integrability of this bound uses:
- **Holder's inequality**: $L^2 \times L^2 \to L^1$
- **Gaussian exponential integrability** (`gff_exp_abs_sum_memLp`): the exponential factor is in $L^2$
- **Gaussian polynomial moments** (`gaussianFreeField_pairing_memLp`): the polynomial factor is in $L^2$

**Lean theorem**: `gff_integrand_fderiv_bound`

### Step 6: Assembly

With all hypotheses verified, `differentiable_integral_of_locally_L1_bound` establishes that
$z \mapsto \int \exp(i\langle\omega, \sum_i z_i J_i\rangle)\  d\mu(\omega)$ is complex Fréchet differentiable on $\mathbb{C}^n$, i.e. satisfies `OS0_Analyticity` as defined in `OSforGFF/OS_Axioms.lean`.

**Lean theorem**: `gaussianFreeField_satisfies_OS0`

### Axioms Used

None (0 `axiom`s, 0 `sorry`s).

## References

- J. Glimm and A. Jaffe, *Quantum Physics*, Springer, 2nd ed., Ch. 6.
- L. Hormander, *An Introduction to Complex Analysis in Several Variables*, North-Holland, 3rd ed., 1990 (Goursat's theorem in n dimensions).
- S. G. Krantz, *Function Theory of Several Complex Variables*, AMS Chelsea, 2001.
- X. Fernique, "Regularite des trajectoires des fonctions aleatoires gaussiennes," Ecole d'Ete de Probabilites de Saint-Flour IV, Springer LNM 480, 1975.
