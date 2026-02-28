# OS4: Clustering and Ergodicity

## Mathematical Background

The OS4 axiom comes in two related forms: **clustering** (distant regions become statistically independent) and **ergodicity** (time averages converge to ensemble averages). For the Gaussian Free Field, clustering follows from the decay of the free propagator, and ergodicity follows from clustering via variance bounds on time averages.

### Key definitions

**Clustering.** For any real test functions $f, g$ and $\varepsilon > 0$, there exists $R > 0$ such that for all translations $a \in \mathbb{R}^4$ with $\|a\| > R$:
$$|Z[f + T_a g] - Z[f] \cdot Z[g]| < \varepsilon$$
where $Z[f] = \int e^{i\langle\omega,f\rangle}\ d\mu(\omega)$ is the generating functional and $T_a g(x) = g(x - a)$ is the spatial translation of $g$.

**Polynomial clustering.** For complex test functions $f, g$ and time translations $T_s$ along the time axis, there exists $c \geq 0$ such that for all $s \geq 0$:
$$\left|M[f, T_s g] - M[f] \cdot M[g]\right| \leq c\ (1+s)^{-\alpha}$$
where $M[f] = \int e^{\langle\omega, f\rangle}\ d\mu(\omega)$ is the moment generating functional (without $i$).

**Ergodicity.** For MGF observables $A(\phi) = \sum_j z_j e^{\langle\phi, f_j\rangle}$, the time average converges to the ensemble average in $L^2(\mu)$:
$$\lim_{T\to\infty} \int_\Omega \left|\frac{1}{T}\int_0^T A(T_s\phi)\ ds - \mathbb{E}_\mu[A(\phi)]\right|^2 d\mu = 0$$

## Proof Strategy

### OS4 Clustering

The proof exploits the **Gaussian factorization formula** for the generating functional:

1. For the GFF, $Z[f] = \exp(-\tfrac{1}{2}C(f,f))$ for real test functions, so the bilinear expansion gives:
$$Z[f + T_a g] = Z[f] \cdot Z[T_a g] \cdot \exp(-S_2(f, T_a g))$$
where $S_2(f, T_a g) = C(f, T_a g)$ is the cross covariance (2-point Schwinger function).

2. By **Euclidean invariance** (OS2): $Z[T_a g] = Z[g]$.

3. The **cross term decays** as $\|a\| \to \infty$ because the propagator $C(x-y) \sim 1/\|x-y\|^2$ at large distances, and the Schwartz test functions provide rapid localization.

4. Since $|Z[f]| \leq 1$ for real test functions and $|e^{-z} - 1| \leq 2|z|$ for $|z| \leq 1$, we conclude $|Z[f + T_ag] - Z[f]Z[g]| \leq 2|S_2(f, T_ag)| \to 0$.

### OS4 Polynomial Clustering

The polynomial clustering with decay exponent $\alpha = 6$ uses the exponential decay of the massive propagator $C(z) \sim e^{-m\|z\|}$ combined with the Schwartz decay of test functions. The bilinear translation decay theorem (`schwartz_bilinear_translation_decay_polynomial`) gives a polynomial bound $c(1+\|a\|)^{-\alpha}$ for any $\alpha > 0$.

### OS4 Ergodicity

The ergodicity proof proceeds through intermediate formulations:

**OS4'' (Polynomial Clustering with $\alpha=6$)** $\Longrightarrow$ **OS4' (Ergodicity on generating functions)** $\Longrightarrow$ **OS4 (Full ergodicity on linear combinations)**

The key steps from clustering to ergodicity are:

1. **Variance bound:** The variance of the time average is bounded by the double time integral of the covariance:
$$\mathrm{Var}\left(\frac{1}{T}\int_0^T A(T_s\phi)\ ds\right) \leq \frac{1}{T^2}\int_0^T\int_0^T |\mathrm{Cov}(s,u)|\ ds\ du$$

2. **Polynomial decay of covariance:** From clustering, the covariance satisfies $|\mathrm{Cov}(s,u)| \leq c(1+|s-u|)^{-\alpha}$.

3. **Double integral bound:** For $\alpha > 1$, the double integral $\int_0^T\int_0^T (1+|s-u|)^{-\alpha}\ ds\ du \leq C \cdot T$ (proved in `double_integral_decay_bound`).

4. **Variance vanishes:** Combining, the variance is $O(1/T) \to 0$ as $T \to \infty$.

5. **Extension to linear combinations:** The single generating function result extends to finite linear combinations $\sum_j z_j e^{\langle\phi, f_j\rangle}$ via the Cauchy-Schwarz inequality for weighted sums (`norm_sq_weighted_sum_le`).

### Literature references

- Glimm-Jaffe, *Quantum Physics*, Chapter 6: Clustering and uniqueness of the vacuum.
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Chapter III: Ergodicity for Gaussian measures.

## Key Declarations

### MGF infrastructure (`OS/OS4_MGF.lean`)

| Declaration | Description |
|-------------|-------------|
| [`timeTranslationE`](../OSforGFF/OS/OS4_MGF.lean#L146) | $T_s \in E(4)$: $T_s(x) = x + se_0$ |
| [`freeCovarianceℂ_bilinear_timeTranslation_invariant`](../OSforGFF/OS/OS4_MGF.lean#L165) | $C(T_sf, T_sg) = C(f,g)$ |
| [`gff_mgf_formula`](../OSforGFF/OS/OS4_MGF.lean#L176) | $\mathbb{E}[e^{\langle\phi, J\rangle}] = e^{\frac{1}{2}C(J,J)}$ |
| [`gff_generating_time_invariant`](../OSforGFF/OS/OS4_MGF.lean#L207) | $Z[T_sf] = Z[f]$ |
| [`gff_joint_mgf_factorization`](../OSforGFF/OS/OS4_MGF.lean#L220) | $\mathbb{E}[e^{\langle\phi,f+g\rangle}] = Z[f]\ Z[g]\ e^{C(f,g)}$ |
| [`exp_sub_one_bound_general`](../OSforGFF/OS/OS4_MGF.lean#L252) | $|e^x - 1| \leq |x| e^{|x|}$ |

### Clustering (`OS/OS4_Clustering.lean`)

| Declaration | Description |
|-------------|-------------|
| [`schwinger2_sum_expansion`](../OSforGFF/OS/OS4_Clustering.lean#L71) | $S_2(f+g, f+g) = S_2(f,f) + 2S_2(f,g) + S_2(g,g)$ |
| [`gff_generating_sum_factorization`](../OSforGFF/OS/OS4_Clustering.lean#L104) | $Z[f+g] = Z[f] \cdot Z[g] \cdot e^{-S_2(f,g)}$ |
| [`gff_generating_norm_le_one_real`](../OSforGFF/OS/OS4_Clustering.lean#L161) | $|Z[f]| \leq 1$ for real $f$ |
| [`GFF_OS4_from_small_decay_real`](../OSforGFF/OS/OS4_Clustering.lean#L197) | $|S_2(f, T_ag)| < \delta \implies |Z[f+T_ag] - Z[f]Z[g]| < 2\delta$ |
| [`schwartz_cross_covariance_decay_real`](../OSforGFF/OS/OS4_Clustering.lean#L336) | $S_2(f, T_ag) \to 0$ as $\lVert a\rVert \to \infty$ |
| [`gaussianFreeField_satisfies_OS4`](../OSforGFF/OS/OS4_Clustering.lean#L475) | **Main clustering theorem**: GFF satisfies `OS4_Clustering` |
| [`freeCovarianceClustering_real`](../OSforGFF/OS/OS4_Clustering.lean#L524) | Covariance clustering for the GFF |
| [`gaussianFreeField_satisfies_OS4_PolynomialClustering`](../OSforGFF/OS/OS4_Clustering.lean#L636) | $\lvert Z[f+T_ag]-Z[f]Z[g]\rvert \le c(1+\lVert a\rVert)^{-\alpha}$ for any $\alpha > 0$ |

### Ergodicity (`OS/OS4_Ergodicity.lean`)

| Declaration | Description |
|-------------|-------------|
| [`OS4'_Ergodicity_generating`](../OSforGFF/OS/OS4_Ergodicity.lean#L82) | Ergodicity for single generating functions $e^{\langle\phi,f\rangle}$ |
| [`OS4''_Clustering`](../OSforGFF/OS/OS4_Ergodicity.lean#L95) | Polynomial clustering with $\alpha = 6$ |
| [`gff_exp_time_translated_memLp_two`](../OSforGFF/OS/OS4_Ergodicity.lean#L125) | $e^{\langle T_s\phi, f\rangle} \in L^2(\mu)$ |
| [`gff_exp_L2_norm_constant`](../OSforGFF/OS/OS4_Ergodicity.lean#L219) | $\lVert e^{\langle T_s\phi, f\rangle}\rVert_{L^2}$ is constant in $s$ |
| [`time_average_memLp_two`](../OSforGFF/OS/OS4_Ergodicity.lean#L267) | $\frac{1}{T}\int_0^T e^{\langle T_s\phi, f\rangle}\ ds \in L^2(\mu)$ |
| [`gff_product_expectation_stationarity`](../OSforGFF/OS/OS4_Ergodicity.lean#L374) | $\mathbb{E}[A(T_s\phi)\overline{A(T_u\phi)}]$ depends only on $s-u$ |
| [`gff_covariance_continuous`](../OSforGFF/OS/OS4_Ergodicity.lean#L497) | $s \mapsto \mathrm{Cov}(A(T_s\phi), A(\phi))$ is continuous |
| [`L2_time_average_variance_bound`](../OSforGFF/OS/OS4_Ergodicity.lean#L577) | $\mathrm{Var}(\frac{1}{T}\int_0^T A_s) \le \frac{1}{T^2}\int_0^T\int_0^T \lvert\mathrm{Cov}(s,u)\rvert\ ds\ du$ |
| [`double_integral_decay_bound`](../OSforGFF/OS/OS4_Ergodicity.lean#L361) | $\int_0^T\int_0^T(1+\lvert s-u\rvert)^{-3}\ ds\ du \leq 2TC$ |
| [`clustering_implies_covariance_decay`](../OSforGFF/OS/OS4_Ergodicity.lean#L722) | $\lvert\mathrm{Cov}(s,u)\rvert \leq c(1+\lvert s-u\rvert)^{-\alpha}$ |
| [`variance_decay_from_clustering`](../OSforGFF/OS/OS4_Ergodicity.lean#L886) | $\mathrm{Var}(\text{time avg}) = O(1/T) \to 0$ |
| [`OS4'_implies_OS4`](../OSforGFF/OS/OS4_Ergodicity.lean#L1070) | Single-function ergodicity $\implies$ linear-combination ergodicity |
| [`OS4''_implies_OS4'`](../OSforGFF/OS/OS4_Ergodicity.lean#L1318) | Polynomial clustering $\implies$ single-function ergodicity |
| [`OS4''_implies_OS4_Ergodicity`](../OSforGFF/OS/OS4_Ergodicity.lean#L1330) | Polynomial clustering $\implies$ full ergodicity |
| [`OS4_PolynomialClustering_implies_OS4_Ergodicity`](../OSforGFF/OS/OS4_Ergodicity.lean#L1339) | **Main ergodicity theorem**: polynomial clustering ($\alpha=6$) $\implies$ `OS4_Ergodicity` |

## Detailed Proof Outline

### Clustering proof chain

```
schwartz_bilinear_translation_decay         (General/SchwartzTranslationDecay)
  -- Bilinear integral of Schwartz functions against decaying kernel vanishes
  -- at large separations.
        |
        v
schwartz_cross_covariance_decay_real        (OS4_Clustering.lean)
  -- Specialize to the free covariance kernel C(x,y), which decays like 1/|x-y|^2.
  -- For any eps > 0, exists R > 0 s.t. |S_2(f, T_a g)| < eps for ||a|| > R.
        |
        v
gff_generating_sum_factorization            (OS4_Clustering.lean)
  -- Z[f+g] = Z[f] * Z[g] * exp(-S_2(f,g))
  -- Gaussian algebraic identity.
        |
        v
GFF_OS4_from_small_decay_real               (OS4_Clustering.lean)
  -- When |S_2(f, T_a g)| < delta <= 1:
  --   ||Z[f + T_a g] - Z[f]Z[g]|| < 2*delta
  -- Uses |Z[f]| <= 1 and exponential estimate.
        |
        v
gaussianFreeField_satisfies_OS4             (OS4_Clustering.lean)
  -- Assembles the above for any eps > 0.
```

### Ergodicity proof chain

```
gaussianFreeField_satisfies_OS4_PolynomialClustering  (OS4_Clustering.lean)
  -- GFF satisfies OS4_PolynomialClustering for alpha = 6.
  -- Uses schwartz_bilinear_translation_decay_polynomial.
        |
        v
clustering_implies_covariance_decay         (OS4_Ergodicity.lean)
  -- Polynomial clustering implies:
  --   |Cov(s,u)| <= c * (1 + |s-u|)^{-alpha}
        |
        v
variance_decay_from_clustering              (OS4_Ergodicity.lean)
  -- Var(time average) <= (1/T^2) * integral of covariance
  --   <= (1/T^2) * C*T = C/T -> 0 as T -> infinity.
  -- Uses double_integral_decay_bound for alpha = 3 > 1.
        |
        v
OS4''_implies_OS4'                          (OS4_Ergodicity.lean)
  -- Polynomial clustering -> single generating function ergodicity.
        |
        v
OS4'_implies_OS4                            (OS4_Ergodicity.lean)
  -- Single generating function ergodicity -> linear combination ergodicity.
  -- Uses norm_sq_weighted_sum_le (Cauchy-Schwarz for weighted sums).
        |
        v
OS4_PolynomialClustering_implies_OS4_Ergodicity   (OS4_Ergodicity.lean)
  -- Composes the chain for alpha = 6.
```

### Key technical results proved along the way

- **L2 membership of time-translated exponentials** (`gff_exp_time_translated_memLp_two`): Uses the Gaussian MGF formula to show $\mathbb{E}[|e^{\langle T_s\phi, f\rangle}|^2] < \infty$.

- **Stationarity of product expectations** (`gff_product_expectation_stationarity`): The covariance $\mathrm{Cov}(s,u)$ depends only on $s - u$, using time-translation invariance of the GFF covariance form.

- **Continuity of the covariance function** (`gff_covariance_continuous`): Uses the algebraic structure of Gaussian measures (stationarity + MGF factorization) and continuity of the covariance form under time translation.

- **Time average is in L2** (`time_average_memLp_two`): Uses the uniform L2 bound (constant in $s$) and Fubini's theorem.

## References

- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*, 2nd ed., Springer, 1987, Chapter 6.
- B. Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*, Princeton University Press, 1974, Chapter III.
- G.B. Folland, *Real Analysis*, 2nd ed., Wiley, 1999 (Fubini-Tonelli theorem for variance bounds).
