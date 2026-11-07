# Short derivations for entries of GAPS.md

[GAPS.md](GAPS.md) selects principal theorem statements of core statistics
and data science that are not proved in Mathlib, TauCeti, or Statlib. None of
the three libraries states the **110 statements** below, or the parts of them delimited by a
**Scope** paragraph. Each follows from results that the libraries do prove,
by a comparatively short argument: a combination of existing theorems, a
specialization, a finite calculation, or a construction packaged in a new
definition. They stay in `GAPS.md` because they belong to the core knowledge
of statistics. This file gives, for each of them, an outline of the argument
and the library results it uses. It follows the corresponding file of the
sibling analysis project, [CKMA GAPS_EASY.md](../lean-CKMA/GAPS_EASY.md).

The proportion is higher than in the analysis project. Much of the
statistics of a graduate course is a short argument from probability,
measure theory, and linear algebra once the statistical notions are
defined. Mathlib already represents measurable parametrized models by
data-generating Markov kernels and randomized estimators by Markov kernels,
and supplies their risk integrals, average risk, Bayes risk, and minimax
risk in `Mathlib.Probability.Decision`. Statlib builds on that framework
the Bayes risk of binary tests, the total-variation testing identity, and
Bayes rules under 0–1 loss (`Statlib/Testing/Binary.lean`). Dedicated
notions of sufficiency, tests of a given size, and sampling or experimental
designs are absent from all three libraries. Many arguments
below introduce these missing notions while reusing the existing model
and risk framework; a new name for a kernel or integral is not a new
mathematical foundation.

The library revisions are those recorded in `GAPS.md`:

- Mathlib `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b` (5 November 2026)
- TauCeti `afa08a3ed16fb167e35de371afb1eb03fbc5913a` (6 November 2026)
- Statlib `eeaac0283690efaa60c31115400cf561836baeb9` (5 November 2026)

Paths are relative to the root of the respective repository.

## How to read the entries

Entries follow the order and section headings of `GAPS.md`. Each entry has
the following parts.

- **Statement:** the entry as it appears in `GAPS.md`, including its
  account of what the libraries already contain.
- **Scope:** present only when the short argument covers just part of the
  statement (53 entries). The rest of that statement remains a
  substantial gap.
- **Argument:** an outline of the proof from library results. Where a
  hypothesis of the statement is not needed, or a degenerate case or a
  measurability condition needs care, the argument says so.
- **Library results:** the declarations and files used.

Every declaration and file named here was located in the sources at the
revisions above. Admissions, acquisition targets and roadmap text were not
used. Local theorem formulations, their exact scopes, completed proofs,
admissions, and compiled axiom audits are tracked separately in
[FORMALIZATION.md](FORMALIZATION.md). "Short" describes the mathematics.
Some arguments still need definitions, transport between formulations, or
measurability code, and none of this is an estimate of the effort needed to
formalize them. An entry of `GAPS.md` that is absent here is
not thereby certified to lack a short proof.

## Index

- **101.** 101.5 Completeness in a full-rank exponential family; 101.7 Rao–Blackwell theorem; 101.8 Lehmann–Scheffé theorem; 101.9 Basu's theorem; 101.10 Information inequality; 101.12 Characterization of UMVU estimators; 101.14 Neyman–Pearson lemma; 101.15 Karlin–Rubin theorem; 101.17 Gaussian sampling distributions; 101.21 Distribution of order statistics; 101.32 Value of a finite statistical game; 101.37 Complete classes; 101.39 Hunt–Stein theorem, compact form; 101.47 Generalized Neyman–Pearson lemma; 101.49 Neyman structure; 101.53 Karlin–Rubin complete class theorem; 101.54 Least favorable distributions; 101.58 Blyth's method; 101.60 Scheffé's method; 101.64 Stein's identity and unbiased risk estimation.
- **102.** 102.1 Delta method; 102.8 Nondegenerate $U$-statistics; 102.12 Contiguity; 102.23 Consistency of $M$-estimators; 102.31 Pearson's multinomial tests; 102.44 $M$-estimators and the Huber minimax property.
- **103.** 103.1 Kolmogorov–Smirnov statistic; 103.8 Representer theorem; 103.17 Cramér–von Mises and two-sample Kolmogorov–Smirnov limits; 103.31 Optimality of functional principal components; 103.34 Lasso under compatibility; 103.37 Benjamini–Hochberg procedure; 103.39 Le Cam's two-point method; 103.40 Fano's method; 103.45 Varshamov–Gilbert bound; 103.46 Assouad's lemma; 103.48 Restricted nullspace and exact recovery; 103.52 Thresholded covariance estimation; 103.54 Perturbation of the leading eigenvector.
- **104.** 104.10 Highest posterior density regions; 104.14 Tweedie's formula and Robbins' estimator; 104.17 Doob's consistency theorem; 104.22 Metropolis–Hastings; 104.32 Independence and random-walk samplers; 104.35 Hamiltonian Monte Carlo; 104.68 Score error and total variation; 104.77 Half-bridges and iterative proportional fitting.
- **105.** 105.1 Gauss–Markov theorem; 105.2 Normal sampling theory; 105.10 Exact tests of nested linear models; 105.15 Distribution of quadratic forms; 105.22 Wishart distribution and Hotelling's $T^2$; 105.28 Gaussian covariance likelihood; 105.37 Kiefer–Wolfowitz equivalence; 105.38 Randomization test; 105.42 Fisher's inequality and optimality of balanced incomplete blocks; 105.44 Latin squares and mutually orthogonal sets; 105.72 Horvitz–Thompson estimation and design variance; 105.73 Simple and stratified random sampling; Neyman allocation; 105.46 Neyman's theorem; 105.47 Identification by regression and by weighting; 105.48 Propensity score; 105.50 Local average treatment effect.
- **106.** 106.12 Long-run variance of a sample mean; 106.14 Herglotz theorem and rational spectral densities; 106.18 Stationarity of GARCH$(1,1)$; 106.24 Bochner's theorem and the Matérn family; 106.37 Sequential probability ratio test; 106.38 Ville's inequality and e-values; 106.41 Wald's fundamental identity and the operating characteristic; 106.42 Anscombe's theorem; 106.44 Optimality of CUSUM; 106.48 Extremal index; 106.50 Poisson approximation for exceedances.
- **107.** 107.2 Rademacher bound; 107.5 Hedge; 107.6 Split conformal prediction; 107.7 No free lunch; 107.8 Bayes classification risk; 107.10 Margin bound; 107.11 Comparison inequality for convex surrogates; 107.12 Generalization of stable algorithms; 107.24 AdaBoost: training error and margins; 107.26 Variational representation of the cumulant function; 107.31 Ridgeless least squares; 107.40 Implicit bias of gradient descent; 107.52 Adversarial bandits; 107.59 Sample complexity with a generative model; 107.60 Temporal differences with linear features; 107.65 Composition; 107.74 Sparse vector technique; 107.75 Contraction under local privacy.
- **108.** 108.1 Cheeger inequality for the normalized Laplacian; 108.8 Classical multidimensional scaling; 108.10 Extrinsic projection mean; 108.21 Čech, Rips, and the nerve; 108.23 Central limit theorem for landscapes; 108.24 Stability of the distance to a measure; 108.42 Consistency of Brenier maps; 108.43 Gromov–Wasserstein distance; 108.44 Debiased Sinkhorn divergence; 108.46 Gaussian transport and barycenters; 108.50 Minimax lower bounds for transport estimation; 108.51 Smooth laws and smoothed distances; 108.56 Semidiscrete dual; 108.57 Tangent-space linearization; 108.59 Procrustes iteration for barycenters; 108.68 Criteria for characteristic kernels; 108.70 Metrization of weak convergence; 108.74 Random Fourier features.

---

## 101. Statistical inference: foundations, decision theory, estimation, and testing

### 101.5. Completeness in a full-rank exponential family

**Statement.** In a minimal full-rank exponential family the natural
statistic $T$ is complete: if $\mathbb E_\eta g(T)=0$ for every $\eta$ in a
nonempty open set, then $g(T)=0$ almost surely under every such $\eta$.
TauCeti proves that a finite measure on the line with finite exponential
moments near zero is determined by its moment generating function there.
After a tilt to the centre of the open set and a split of $g$ into positive
and negative parts, this gives the one-parameter case by a short argument.
Completeness itself is not formulated, and the case $k>1$ needs the
multivariate uniqueness theorem for Laplace transforms.

**Scope.** The argument covers the case $k=1$. For $k>1$ the uniqueness
theorem for multivariate Laplace transforms remains a substantial gap.

**Argument.** Let $\nu$ be the image under $T$ of $h\,d\mu$, so that the law
of $T$ under $\eta$ is $e^{\eta t-A(\eta)}\,\nu(dt)$. Let $g$ be measurable
with $\mathbb E_\eta|g(T)|<\infty$ and $\mathbb E_\eta g(T)=0$ for $\eta$ in
an open interval containing $[\eta_0-\delta,\eta_0+\delta]$. Define the
measures
$$
\nu^\pm(dt)=g^\pm(t)\,e^{\eta_0t}\,\nu(dt).
$$
They are finite. Their moment generating functions at $|s|<\delta$ are
$$
\int e^{st}\,d\nu^\pm=e^{A(\eta_0+s)}\,\mathbb E_{\eta_0+s}\,g^\pm(T),
$$
which is finite, so $0$ is an interior point of the exponential-integrability
set of $\nu^+$. The two moment generating functions agree for $|s|<\delta$,
because $\mathbb E_{\eta}g^+(T)=\mathbb E_\eta g^-(T)$. TauCeti's
determinacy theorem gives $\nu^+=\nu^-$. The measure $\nu^+$ is
concentrated on $\{g>0\}$ and $\nu^-$ on $\{g<0\}$, so
$\nu^+(\mathbb R)=\nu^-(\{g>0\})=0$. Hence $g=0$ $\nu$-almost everywhere.
The law of $T$ under every $\eta$ in the natural parameter space is
absolutely continuous with respect to $\nu$, so $g(T)=0$ almost surely
under every such $\eta$, not only those in the open set. Minimality is not
used when $k=1$.

**Library results.** `TauCeti.Measure.ext_of_mgf` in
`TauCeti/Probability/Moments/Determinacy.lean`; `ProbabilityTheory.mgf` and
`ProbabilityTheory.integrableExpSet` in
`Mathlib/Probability/Moments/Basic.lean` and
`Mathlib/Probability/Moments/IntegrableExpMul.lean`;
`MeasureTheory.integral_withDensity_eq_integral_smul` in
`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`.

### 101.7. Rao–Blackwell theorem

**Statement.** Let $T$ be sufficient and let $\delta$ be an estimator with
$\mathbb E_\theta|\delta|<\infty$. Then
$\delta^\star(T)=\mathbb E_\theta[\delta\mid T]$ does not depend on
$\theta$ and has the same expectation as $\delta$. For a loss $L(\theta,a)$
convex in $a$, it satisfies
$\mathbb E_\theta L(\theta,\delta^\star(T))\le\mathbb E_\theta
L(\theta,\delta(X))$. Mathlib's conditional Jensen inequality gives the
risk reduction for a single law after taking expectations. Once
sufficiency is defined, the theorem follows by that short argument, since
sufficiency supplies the independence of $\theta$.

**Argument.** Sufficiency must first be defined. Following the section
preamble of `GAPS.md`, call $T:\mathcal X\to\mathcal T$, on a standard Borel
sample space, sufficient when there is one Markov kernel
$\kappa:\mathcal T\to\mathcal X$ such that, for every $\theta$,
Mathlib's regular conditional distribution
$\mathop{\mathrm{condDistrib}}(\mathrm{id},T,P_\theta)$ equals $\kappa$
almost everywhere under the law of $T$. Then, for integrable $f$,
$$
\mathbb E_\theta[f\mid T]=\Bigl(t\mapsto\int f\,d\kappa(t)\Bigr)\circ T
\quad P_\theta\text{-a.s.},
$$
and the right side does not depend on $\theta$. This identity supplies the
independence of $\theta$ here and in 101.8, 101.9, 101.12 and 101.49.

Put $\delta^\star(t)=\int\delta\,d\kappa(t)$. By the identity,
$\delta^\star(T)$ is a version of $\mathbb E_\theta[\delta\mid T]$ for
every $\theta$. Its expectation is $\mathbb E_\theta\delta$ by the
tower property. Fix $\theta$ and take a real action space. The function
$a\mapsto L(\theta,a)$ is convex on $\mathbb R$ and hence continuous. If
$\mathbb E_\theta L(\theta,\delta)=\infty$ there is nothing to prove.
Otherwise $L(\theta,\delta)$ is integrable, because a convex function lies
above an affine function and $\delta$ is integrable. Conditional Jensen with
$s=\mathbb R$ gives
$L(\theta,\mathbb E_\theta[\delta\mid T])\le\mathbb E_\theta[L(\theta,\delta)\mid T]$
almost surely. Integrating this inequality gives the risk bound. The same
argument works for a closed convex action set on which $L(\theta,\cdot)$ is
convex and lower semicontinuous.

**Library results.** `ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id`
in `Mathlib/Probability/Kernel/CondDistrib.lean`;
`ConvexOn.map_condExp_le` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean`;
`MeasureTheory.integral_condExp` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`.

### 101.8. Lehmann–Scheffé theorem

**Statement.** Let $T$ be a complete sufficient statistic and let $g(\theta)$
admit an unbiased estimator of finite expectation. Then there is an
unbiased estimator $\varphi(T)$, and any two unbiased functions of $T$ agree
almost surely under every $P_\theta$. For every loss convex in the action,
$\varphi(T)$ minimizes the risk among all unbiased estimators of finite
risk. It follows from 101.7 and completeness by a short argument, but none of the
notions involved is defined.

**Argument.** If $\delta$ is unbiased, then $\varphi=\delta^\star$ from
101.7 is a function of $T$, free of $\theta$, and unbiased. If
$\varphi_1(T)$ and $\varphi_2(T)$ are unbiased, then
$\mathbb E_\theta(\varphi_1-\varphi_2)(T)=0$ for every $\theta$.
Completeness gives $\varphi_1(T)=\varphi_2(T)$ almost surely under every
$P_\theta$. Now let $W$ be any unbiased estimator of finite risk. Then
$W^\star(T)$ is an unbiased function of $T$, so $W^\star(T)=\varphi(T)$
almost surely. By 101.7,
$\mathbb E_\theta L(\theta,\varphi(T))=\mathbb E_\theta L(\theta,W^\star(T))
\le\mathbb E_\theta L(\theta,W)$. Unbiasedness includes integrability, which
is what 101.7 requires.

**Library results.** Those of 101.7.

### 101.9. Basu's theorem

**Statement.** If $T$ is a boundedly complete sufficient statistic and $V$ is
ancillary, then $T$ and $V$ are independent under every $P_\theta$. Not
present in any of the three libraries.

**Argument.** Let $\kappa$ be the kernel of the definition of sufficiency
in 101.7. Fix a measurable set $B$ in the range of $V$. Put
$\psi_B(t)=\kappa(t)(V^{-1}B)$, a measurable function with values in
$[0,1]$ and free of $\theta$. Since $V$ is ancillary,
$c_B=P_\theta(V\in B)$ does not depend on $\theta$. Disintegration of the
law of $(T,X)$ gives
$$
P_\theta(T\in A,\ V\in B)=\int_A\psi_B\,d(P_\theta\circ T^{-1}).
$$
This uses that the law of $(T,X)$ is the law of $T$ composed with
$\mathop{\mathrm{condDistrib}}(\mathrm{id},T,P_\theta)$, and that this
kernel equals $\kappa$ almost everywhere. With $A$ the whole range,
$\mathbb E_\theta(\psi_B(T)-c_B)=0$ for every $\theta$. Bounded
completeness gives $\psi_B(T)=c_B$ almost surely under every $P_\theta$,
so $P_\theta(T\in A,V\in B)=P_\theta(T\in A)\,P_\theta(V\in B)$. This is
independence.

**Library results.** `ProbabilityTheory.compProd_map_condDistrib` in
`Mathlib/Probability/Kernel/CondDistrib.lean`;
`ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul` in
`Mathlib/Probability/Independence/Basic.lean`.

### 101.10. Information inequality

**Statement.** Let $\theta$ range over an open subset of $\mathbb R^k$. Let
the support be free of $\theta$, the density differentiable in $\theta$,
and the information matrix $I(\theta)$ nonsingular. Let $W$ be an unbiased
estimator of a differentiable $g:\Theta\to\mathbb R^m$ with
$\mathbb E_\theta\|W\|^2<\infty$. Assume that differentiation in each
$\theta_j$ may be passed under the integrals
$\int Wf(\cdot\mid\theta)\,d\mu$ and $\int f(\cdot\mid\theta)\,d\mu$. Then
$$\mathop{\mathrm{Cov}}_\theta(W)\ge Dg(\theta)\,I(\theta)^{-1}\,Dg(\theta)^\top$$
in the Loewner order. For a real parameter this reads
$\mathop{\mathrm{Var}}_\theta W\ge g'(\theta)^2/I(\theta)$, and for an
independent sample $I(\theta)$ is replaced by $nI_1(\theta)$. Fisher
information and the score are not defined. The ingredients are available
in general form: Mathlib's differentiation under the integral sign with a
dominated derivative, covariance bilinearity and Cauchy–Schwarz, and the
Loewner order. Statlib's quadratic-mean differentiability, with a score of
mean zero, is a starting point for the score under weaker regularity.

**Argument.** Define the score
$S_j=\partial_{\theta_j}f(\cdot\mid\theta)/f(\cdot\mid\theta)$ on the common
support. Off the support, $f(x\mid\cdot)$ vanishes identically, so
$\partial_jf=0$ there. The two interchange hypotheses give
$\mathbb E_\theta S_j=\partial_j\int f\,d\mu=0$ and
$\mathbb E_\theta[WS_j]=\partial_j g(\theta)$. Since $S\in L^2$ by the
definition of $I(\theta)$, this says
$\mathop{\mathrm{Cov}}_\theta(W,S)=Dg(\theta)$. For $a\in\mathbb R^m$ put
$b=I(\theta)^{-1}Dg(\theta)^\top a$. Bilinearity of covariance gives
$$
0\le\mathop{\mathrm{Var}}_\theta(a^\top W-b^\top S)
=a^\top\mathop{\mathrm{Cov}}_\theta(W)a
-a^\top Dg(\theta)I(\theta)^{-1}Dg(\theta)^\top a .
$$
For an independent sample, the score of the product density is the sum of
the $n$ independent, centred one-observation scores. Its covariance is
therefore $nI_1(\theta)$. The interchange hypotheses are then those of the
$n$-sample model. They are hypotheses of the statement; where they are to
be verified, Mathlib's differentiation under the integral sign with an
integrable bound on the derivative gives them.

**Library results.** `ProbabilityTheory.covariance` and its bilinearity
lemmas in `Mathlib/Probability/Moments/Covariance.lean`;
`hasFDerivAt_integral_of_dominated_of_fderiv_le` in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`, for the interchange
hypotheses;
`ProbabilityTheory.variance_nonneg` and `IndepFun.variance_sum` in
`Mathlib/Probability/Moments/Variance.lean`; the Loewner order
`Matrix.instPartialOrder` in `Mathlib/Analysis/Matrix/Order.lean`.

### 101.12. Characterization of UMVU estimators

**Statement.** Let $W$ be an unbiased estimator of $g(\theta)$ with
$\mathbb E_\theta W^2<\infty$ for every $\theta$. Then $W$ has minimal
variance at every $\theta$ among unbiased estimators $W'$ of $g(\theta)$
with $\mathbb E_\theta W'^2<\infty$ for every $\theta$ if and only if $\mathop{\mathrm{Cov}}_\theta(W,U)=0$ for every $\theta$ and every
statistic $U$ with $\mathbb E_\theta U=0$ and $\mathbb E_\theta U^2<\infty$
for every $\theta$. If $T$ is sufficient and $W=h(T)$, it suffices to test
functions $U$ of $T$. Such an estimator is unique almost surely under every
$P_\theta$. Mathlib's $L^2$ projection property of conditional expectation
is the underlying Hilbert-space fact; the statement is absent.

**Argument.** The competitors are taken, like the $U$, in the class of
unbiased estimators with $\mathbb E_\theta W'^2<\infty$ for every $\theta$;
otherwise the difference $W'-W$ is not an admissible $U$.

- *Minimality implies orthogonality.* If $W$ is minimal, then $W+\lambda U$
  is unbiased for every real $\lambda$. Hence
  $2\lambda\mathop{\mathrm{Cov}}_\theta(W,U)+\lambda^2\mathop{\mathrm{Var}}_\theta U\ge0$
  for all $\lambda$, which forces $\mathop{\mathrm{Cov}}_\theta(W,U)=0$.
- *Orthogonality implies minimality.* For an unbiased $W'$ put $U=W'-W$.
  Then $\mathop{\mathrm{Cov}}_\theta(W,U)=0$ gives
  $\mathop{\mathrm{Var}}_\theta W'=\mathop{\mathrm{Var}}_\theta W
  +\mathop{\mathrm{Var}}_\theta U$.
- *Uniqueness.* If $W'$ is also minimal, then
  $\mathop{\mathrm{Var}}_\theta U=0$. A centred variable with zero variance
  vanishes almost surely, so $U=0$.
- *Reduction to functions of $T$.* For a general $U$, put
  $V=\mathbb E[U\mid T]$. By sufficiency it is a function of $T$ free of
  $\theta$, and it satisfies $\mathbb E_\theta V=0$ and
  $\mathbb E_\theta V^2\le\mathbb E_\theta U^2$. Pulling out $h(T)$ gives
  $\mathbb E_\theta[h(T)U]=\mathbb E_\theta[h(T)V]$, so
  $\mathop{\mathrm{Cov}}_\theta(W,U)=\mathop{\mathrm{Cov}}_\theta(W,V)$.

**Library results.** `ProbabilityTheory.variance_add` and
`ProbabilityTheory.ae_eq_integral_of_variance_eq_zero` in
`Mathlib/Probability/Moments/Variance.lean`;
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean`;
`MeasureTheory.integral_condExp`; `ConvexOn.map_condExp_le` for the bound
$\mathbb E V^2\le\mathbb E U^2$;
`ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id`.

### 101.14. Neyman–Pearson lemma

**Statement.** Let $P_0,P_1$ have densities $f_0,f_1$ with respect to $\mu$
and let $0<\alpha<1$. There are $k\ge0$ and a test $\varphi$ with
$\mathbb E_{P_0}\varphi=\alpha$, $\varphi=1$ where $f_1>kf_0$ and
$\varphi=0$ where $f_1<kf_0$. Any such test is most powerful of level
$\alpha$. Every most powerful level-$\alpha$ test agrees with it
$(P_0+P_1)$-almost everywhere off $\{f_1=kf_0\}$. Statlib treats a simple
binary test as a Markov kernel into $\{0,1\}$ assessed by its Bayes risk
under the $0$–$1$ loss: for prior weights $\pi_0,\pi_1$ the Bayes risk is
the infimum over measurable regions $E$ of $\pi_0P_0(E)+\pi_1P_1(E^c)$, and
the likelihood-ratio test that decides for $P_1$ where
$\pi_0\,dP_0\le\pi_1\,dP_1$ is a Bayes test. This is the Lagrangian form of
the construction; tests of prescribed size, the existence of $k$ and of the
randomization, and uniqueness are not stated in any library. Optimality
follows from the pointwise inequality $(\varphi-\varphi')(f_1-kf_0)\ge0$ by
integration. Existence of $k$ and of the randomization constant uses the
distribution function of $f_1/f_0$ under $P_0$.

**Argument.** *Existence.* Put $Z=f_1/f_0$ on $\{f_0>0\}$ and $Z=0$
elsewhere; the set $\{f_0=0\}$ is $P_0$-null. Let $G$ be the law of $Z$
under $P_0$, a probability measure on $[0,\infty)$, and let $k$ be the
quantile of $G$ at level $1-\alpha$. Then $k\ge0$. The quantile
inequalities give
$$
P_0(Z>k)\le\alpha\le P_0(Z\ge k).
$$
Let $\varphi$ be $1$ on $\{f_1>kf_0\}$, $0$ on $\{f_1<kf_0\}$, and $\gamma$
on $\{f_1=kf_0\}$. Here $\gamma=(\alpha-P_0(Z>k))/P_0(Z=k)$ if
$P_0(Z=k)>0$, and $\gamma$ is arbitrary otherwise. On $\{f_0>0\}$ these
three sets are $\{Z>k\}$, $\{Z<k\}$ and $\{Z=k\}$, so
$\mathbb E_0\varphi=\alpha$.

*Optimality.* Let $\varphi'$ be a test with $\mathbb E_0\varphi'\le\alpha$.
The product $(\varphi-\varphi')(f_1-kf_0)$ is nonnegative pointwise. Its
integral is
$(\mathbb E_1\varphi-\mathbb E_1\varphi')-k(\mathbb E_0\varphi-\mathbb E_0\varphi')$,
so $\mathbb E_1\varphi\ge\mathbb E_1\varphi'$.

*Uniqueness.* If $\varphi'$ is also most powerful, the same integral equals
$-k(\alpha-\mathbb E_0\varphi')\le0$. A nonnegative integrable function
with nonpositive integral vanishes $\mu$-almost everywhere. Hence
$\varphi=\varphi'$ $\mu$-almost everywhere off $\{f_1=kf_0\}$, and so
$(P_0+P_1)$-almost everywhere there. The optimality part holds for any test
of this form with any $k\ge0$, whatever its size.

Statlib's Bayes form does not shorten the argument: it minimizes
$\pi_0\mathbb E_0\varphi+\pi_1(1-\mathbb E_1\varphi)$ without a size
constraint. With $\pi_0/\pi_1=k$ the nonrandomized likelihood-ratio test
it constructs has the form above, and its Bayes optimality gives the
optimality of that particular test among tests of no larger size. The
size $\alpha$ still has to be reached by the choice of $k$ and $\gamma$,
which needs the randomized test of the existence step.

**Library results.** `MeasureTheory.Measure.quantile`,
`MeasureTheory.Measure.le_cdf_quantile` and
`MeasureTheory.Measure.measureReal_Iio_quantile_le` in
`TauCeti/Probability/Quantile.lean`;
`MeasureTheory.integral_eq_zero_iff_of_nonneg` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`;
`MeasureTheory.integral_withDensity_eq_integral_smul` for
$\mathbb E_i\varphi=\int\varphi f_i\,d\mu$.

### 101.15. Karlin–Rubin theorem

**Statement.** Let the family, with $\Theta\subset\mathbb R$, have monotone
likelihood ratio in $T$. Let $\theta_0\in\Theta$ and $0<\alpha<1$. Consider
a test with $\varphi=1$ for $T>c$, $\varphi=\gamma$ for $T=c$, $\varphi=0$
for $T<c$, and size $\alpha$ at $\theta_0$. Every such test is UMP of level
$\alpha$ for $\theta\le\theta_0$ against $\theta>\theta_0$, and its power
function is nondecreasing. In particular the one-sided test on the natural
statistic of a one-parameter exponential family is UMP. Absent; it follows
from 101.14 applied pointwise in the alternative.

**Argument.** For $\theta'<\theta''$ write
$f_{\theta''}/f_{\theta'}=H(T)$ with $H$ nondecreasing, taking values in
$[0,\infty]$ with $a/0=\infty$. Extend $H$ monotonically off the range of
$T$ and put $k=H(c)$. If $H(T)>k$ then $T>c$, and if $H(T)<k$ then $T<c$.
So $\varphi$ has the form of 101.14 for $\theta'$ against $\theta''$. Its
optimality part needs only this form and $k<\infty$. When
$\mathbb E_{\theta'}\varphi>0$, the set $\{T\ge c,\ f_{\theta'}>0\}$ has
positive mass, and on it $H(T)<\infty$, so $k<\infty$.

- *Monotone power.* Compare $\varphi$ with the constant test
  $\mathbb E_{\theta'}\varphi$, which has the same size at $\theta'$. This
  gives $\mathbb E_{\theta''}\varphi\ge\mathbb E_{\theta'}\varphi$. When
  $\mathbb E_{\theta'}\varphi=0$ this inequality is trivial.
- *Level on the composite null.* By monotonicity, the size over
  $\theta\le\theta_0$ is $\mathbb E_{\theta_0}\varphi=\alpha$.
- *Uniform optimality.* Any test of level $\alpha$ for the composite null
  has size at most $\alpha$ at $\theta_0$. By 101.14 for $\theta_0$
  against each $\theta_1>\theta_0$, its power at $\theta_1$ is at most that
  of $\varphi$.
- *Exponential families.* The ratio
  $\exp((\eta_1-\eta_0)T-A(\eta_1)+A(\eta_0))$ is increasing in $T$ for
  $\eta_1>\eta_0$.

**Library results.** The integration steps of 101.14; no further library
result is needed.

### 101.17. Gaussian sampling distributions

**Statement.** Let $X_1,\ldots,X_n\sim N(\mu,\sigma^2)$ be independent, with
$\sigma>0$ and $n\ge2$. Put $\bar X=n^{-1}\sum_iX_i$ and
$S^2=(n-1)^{-1}\sum_i(X_i-\bar X)^2$. Then
$\bar X\sim N(\mu,\sigma^2/n)$, $(n-1)S^2/\sigma^2\sim\chi^2_{n-1}$, and
$\bar X$ and $S^2$ are independent. Hence $\sqrt n(\bar X-\mu)/S$ has the
Student $t_{n-1}$ law, and
$\bar X\pm t_{n-1,1-\alpha/2}S/\sqrt n$ has exact coverage $1-\alpha$. For
two independent normal samples, each of size at least two,
$(S_1^2/\sigma_1^2)/(S_2^2/\sigma_2^2)$ has the $F$ law with the sample
sizes minus one as degrees of freedom. Mathlib gives the law of $\bar X$.
TauCeti gives the known-mean chi-squared law, the representations of $t$
and $F$ as ratios of independent Gaussian and chi-squared variables, and,
for the standard Gaussian on a Euclidean space, the independence of its
orthogonal projections onto mutually orthogonal subspaces and the
$\chi^2_{\dim K}$ law of the squared length of its projection onto a
subspace $K$. Missing is the identification of $(n-1)S^2/\sigma^2$ with the
squared projection of the standardized sample onto the orthogonal
complement of the constant vectors, and of $\bar X$ with a function of the
projection onto the constants. The chi-squared law of $S^2$ and its
independence from $\bar X$ then follow from the projection theorems by a
short argument, and the rest from the ratio theorems.

**Argument.** Put $Z_i=(X_i-\mu)/\sigma$. The vector $Z$, read in the
Euclidean space $E=\mathbb R^n$, has the standard Gaussian law, because the
standard Gaussian of $E$ is the image of the product of $N(0,1)$ laws. Let
$K$ be the line spanned by $\mathbf 1=(1,\ldots,1)$ and $K^\perp$ its
orthogonal complement, of dimension $n-1$. The orthogonal projections are
$$
P_KZ=\bar Z\,\mathbf 1,\qquad P_{K^\perp}Z=Z-\bar Z\,\mathbf 1,
\qquad\bar Z=\frac1n\sum_iZ_i .
$$
Then:

- $\bar X=\mu+\sigma\bar Z$ is a function of $P_KZ$, and
  $\bar X\sim N(\mu,\sigma^2/n)$ by Mathlib's sums and scalings of
  independent Gaussians.
- $\|P_{K^\perp}Z\|^2=\sum_i(Z_i-\bar Z)^2=(n-1)S^2/\sigma^2$, which has
  the $\chi^2_{n-1}$ law by TauCeti's projection theorem.
- $K$ and $K^\perp$ are orthogonal, so TauCeti's independence theorem makes
  $P_KZ$ and $P_{K^\perp}Z$ independent. Hence $\bar X$ and $S^2$ are
  independent.
- With $Y_0=\sqrt n\bar Z\sim N(0,1)$ and $V=\|P_{K^\perp}Z\|^2$, the
  statistic is $\sqrt n(\bar X-\mu)/S=Y_0/\sqrt{V/(n-1)}$, which has the
  $t_{n-1}$ law by TauCeti's ratio theorem. This uses $n-1>0$.
- For the $F$ law, $(S_1^2/\sigma_1^2)/(S_2^2/\sigma_2^2)
  =(V_1/(n_1-1))/(V_2/(n_2-1))$ with $V_1,V_2$ independent chi-squared,
  and TauCeti's ratio theorem applies.
- For coverage, the Student law has a continuous distribution function and
  is symmetric. Hence, with $q$ its quantile at $1-\alpha/2$,
  $P(T\le q)=1-\alpha/2$ and $P(T<-q)=\alpha/2$, so $P(|T|\le q)=1-\alpha$.

**Library results.** `map_pi_eq_stdGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`;
`Submodule.map_norm_sq_starProjection_stdGaussian`,
`ProbabilityTheory.HasLaw.norm_sq_orthogonalProjectionOnto_stdGaussian`
and `ProbabilityTheory.HasLaw.iIndepFun_orthogonalProjectionOnto_stdGaussian`
in `TauCeti/Probability/Distributions/Gaussian/Projection.lean`;
`Submodule.starProjection_singleton` and
`Submodule.starProjection_orthogonal_val` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
`Submodule.finrank_orthogonal_span_singleton` in
`Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`;
`Submodule.isOrtho_orthogonal_right` in
`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`;
`ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun`,
`ProbabilityTheory.gaussianReal_map_const_mul` and
`gaussianReal_map_add_const` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`;
`TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared` in
`TauCeti/Probability/Distributions/StudentT/ChiSquared.lean`;
`TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared` in
`TauCeti/Probability/Distributions/FisherSnedecor/ChiSquared.lean`;
`TauCeti.Probability.continuous_cdf_studentTMeasure` in
`TauCeti/Probability/Distributions/StudentT/Cdf.lean`;
`TauCeti.Probability.studentTMeasure_map_neg` in
`TauCeti/Probability/Distributions/StudentT/Basic.lean`;
`MeasureTheory.Measure.cdf_quantile` in `TauCeti/Probability/Quantile.lean`.

### 101.21. Distribution of order statistics

**Statement.** For independent observations with continuous distribution
function $F$ and density $f$, the order statistics have joint density
$n!\prod_if(x_i)$ on $x_1<\cdots<x_n$, and $X_{(j)}$ has density
$$\frac{n!}{(j-1)!(n-j)!}F(x)^{j-1}(1-F(x))^{n-j}f(x).$$
In particular $F(X_{(j)})\sim\mathop{\mathrm{Beta}}(j,n+1-j)$, and the
ranks are uniform on the $n!$ permutations and independent of the ordered
sample. TauCeti proves that the law of the sorted sample of an atomless
independent identically distributed sample is $n!$ times the product law
restricted to the strictly increasing chamber, and, for every law, atoms
included, the distribution function of a single order statistic and its
representation as the quantile image of a beta law. The joint density is
one step from the chamber formula, and the beta law of $F(X_{(j)})$ two
steps from the quantile representation and the probability integral
transform. Missing are the explicit marginal density for general $F$, and
the law of the ranks with its independence from the order statistic.

**Scope.** The argument proves the joint density and the beta law of
$F(X_{(j)})$; the latter uses only the continuity of $F$. The marginal
density of $X_{(j)}$ and the law of the ranks remain substantial gaps.

**Argument.** *Joint density.* A continuous distribution function has no
atoms, so TauCeti's chamber formula applies: the sorted sample has the law
$n!\,P^{\otimes n}$ restricted to $C=\{x_1<\cdots<x_n\}$, with $P$ the
common law. With $P=f\,dx$, the product law has density
$\prod_if(x_i)$ with respect to Lebesgue measure on $\mathbb R^n$, and its
restriction to the measurable set $C$ has density
$\mathbf 1_C\prod_if(x_i)$. So the sorted sample has density
$n!\prod_if(x_i)$ on $C$.

*Beta law of $F(X_{(j)})$.* With zero-based index $k=j-1$, TauCeti
represents the law of $X_{(j)}$ as the image of
$\mathop{\mathrm{Beta}}(k+1,n-k)$ under the quantile function $F^{-1}$.
Hence $F(X_{(j)})$ has the image of the same beta law under $F\circ F^{-1}$.
For continuous $F$, $F(F^{-1}(u))=u$ for $0<u<1$. The beta law is
concentrated on $(0,1)$, so the image is $\mathop{\mathrm{Beta}}(j,n+1-j)$.

**Library results.** `TauCeti.Probability.map_orderStatistics_pi` in
`TauCeti/Probability/Distributions/OrderStatistic/Joint.lean`;
`TauCeti.pi_withDensity` in
`TauCeti/MeasureTheory/Measure/PiWithDensity.lean`;
`MeasureTheory.restrict_withDensity` in
`Mathlib/MeasureTheory/Measure/WithDensity.lean`;
`TauCeti.measurableSet_setOf_strictMono` in
`TauCeti/MeasureTheory/MeasurableSpace/StrictMono.lean`;
`TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile` in
`TauCeti/Probability/Distributions/OrderStatistic/Basic.lean`;
`MeasureTheory.Measure.cdf_quantile` in `TauCeti/Probability/Quantile.lean`;
`TauCeti.Probability.ae_mem_Ioo_betaMeasure` in
`TauCeti/Probability/Distributions/Beta/Basic.lean`.

### 101.32. Value of a finite statistical game

**Statement.** If $\Theta$ and $\mathcal A$ are finite, then the minimax
risk equals the supremum over priors of the minimal Bayes risk, a minimax
rule exists, and a least favorable prior exists. Mathlib proves that the
maximal Bayes risk is at most the minimax risk, and it proves Sion's
minimax theorem. The equality follows by identifying randomized rules on a
finite action space, through their risk vectors, with a compact convex set
on which the Bayes risk is bilinear, and applying Sion's theorem. This
identification and the existence statements are missing.

**Scope.** The argument proves the equality of the minimax risk with the
maximal Bayes risk and the existence of a least favorable prior. Existence
of a minimax rule needs the risk set to be closed. That holds, but its
proof needs weak-$*$ compactness of randomized rules in
$L^\infty$, which remains a gap.

**Argument.** A real loss on finite $\Theta\times\mathcal A$ is bounded.
After adding a constant it is nonnegative, as in Mathlib's setting, and
this shifts all risks, Bayes risks and the minimax risk by the same
constant. Let $S\subset\mathbb R^\Theta$ be the set of risk vectors
$(R(\theta,\delta))_\theta$ of Markov kernels $\delta$. It is bounded. It is
convex, because a convex combination of Markov kernels is a Markov kernel
and composition with $P$ is additive in the kernel. Put $\bar S$ for its
compact convex closure and $\Delta$ for the simplex of priors. The function
$f(\pi,s)=\pi\cdot s$ is bilinear and continuous on $\Delta\times\bar S$.
Sion's theorem gives a saddle point $(\pi^*,s^*)$, so that
$$
\min_{s\in\bar S}\max_\pi\pi\cdot s=\pi^*\cdot s^*
=\max_\pi\min_{s\in\bar S}\pi\cdot s .
$$
The functions $s\mapsto\max_\pi\pi\cdot s$ and $s\mapsto\pi\cdot s$ are
continuous, so their infima over $S$ and over $\bar S$ coincide. The left
side is therefore the minimax risk. With the finite-sum form of the Bayes
risk, the right side is $\sup_\pi$ of the Bayes risk. The prior $\pi^*$
attains this supremum, so it is least favorable.

**Library results.** `Sion.exists_isSaddlePointOn` in
`Mathlib/Topology/Sion.lean`; `ProbabilityTheory.minimaxRisk` and
`ProbabilityTheory.bayesRisk` in `Mathlib/Probability/Decision/Risk/Defs.lean`;
`ProbabilityTheory.iSup_bayesRisk_le_minimaxRisk` in
`Mathlib/Probability/Decision/Risk/Basic.lean`;
`ProbabilityTheory.bayesRisk_fintype` and `avgRisk_fintype` in
`Mathlib/Probability/Decision/Risk/Countable.lean`;
`ProbabilityTheory.Kernel.comp_add_left` in
`Mathlib/Probability/Kernel/Composition/Comp.lean`.

### 101.37. Complete classes

**Statement.** Let $\Theta$ be finite. Every admissible rule is Bayes for
some prior. Suppose the risk set
$\{(R(\theta,\delta))_\theta\}\subset\mathbb R^\Theta$ of randomized rules
is bounded from below and closed from below: it contains every point $x$
of its closure such that no other point $y$ of the closure has $y\le x$
coordinatewise. Then the Bayes rules form a complete class, and the
admissible Bayes rules form a minimal complete class. With the loss bounded
below, both conditions hold when the action space is finite, or a closed
bounded subset of Euclidean space with $a\mapsto L(\theta,a)$ continuous.
Admissibility and complete classes are not defined; the
separating-hyperplane argument is absent.

**Scope.** The argument proves the first two assertions, with minimality
understood up to risk equivalence. As in the statement, risks are taken
finite. The sufficient conditions in the last sentence remain a gap: as in
101.32, their proof needs compactness of the risk set.

**Argument.** The risk set $S$ is convex, as in 101.32.

- *Admissible rules are Bayes.* Let $\delta$ be admissible with risk point
  $r$. Then $S$ is disjoint from the open convex set
  $Q=r-(0,\infty)^\Theta$. Indeed, a point of $S\cap Q$ would dominate $r$
  strictly in every coordinate. Separation gives a nonzero linear
  functional $\pi$ with $\pi\cdot q<\pi\cdot s$ for $q\in Q$, $s\in S$.
  Letting one coordinate of $q$ tend to $-\infty$ shows $\pi\ge0$.
  Normalizing $\pi$ and letting $q\to r$ gives $\pi\cdot r\le\pi\cdot s$
  for all $s\in S$. So $\delta$ is Bayes for the prior $\pi$.
- *Bayes rules form a complete class.* Let $s\in S$. The set
  $\bar S\cap\{x\le s\}$ is closed and bounded, hence compact, because $S$
  is bounded from below. A minimizer $x_0$ of $\sum_\theta x_\theta$ on it
  is a lower boundary point of $\bar S$. Closedness from below puts $x_0$
  in $S$. Then $x_0$ is the risk point of a rule that is admissible, and
  hence Bayes by the first part, and $x_0\le s$.
- *Minimality.* Every complete class contains, for each admissible
  $\delta$, a rule with the same risk.

**Library results.** `geometric_hahn_banach_open` in
`Mathlib/Analysis/LocallyConvex/Separation.lean`;
`Metric.isCompact_of_isClosed_isBounded` in
`Mathlib/Topology/MetricSpace/Bounded.lean`; `IsCompact.exists_isMinOn` in
`Mathlib/Topology/Order/Compact.lean`; the risk vocabulary of 101.32.

### 101.39. Hunt–Stein theorem, compact form

**Statement.** Let the model and the loss be invariant, and let the loss be
bounded below. Let $G$ be a compact group with normalized Haar measure
$\nu$, acting jointly measurably on samples, parameters and actions. For
every randomized rule $\delta$, Haar averaging gives an equivariant
randomized rule $\bar\delta$ with
$R(\theta,\bar\delta)=\int_GR(g\theta,\delta)\,\nu(dg)$. Hence the maximum
risk does not increase, the minimax value equals the infimum of the maximum
risk over equivariant rules, and an equivariant minimax rule exists
whenever a minimax rule exists. Mathlib's Haar measure is the starting point;
group actions on models are
not formulated.

**Argument.** After a shift, the loss is nonnegative. Define the averaged
rule
$$
\bar\delta(x)(B)=\int_G\delta(g^{-1}x)(g^{-1}B)\,\nu(dg).
$$
It is the image under $(g,a)\mapsto ga$ of the composition-product of the
constant kernel $\nu$ with $(x,g)\mapsto\delta(g^{-1}x)$, and is therefore
a Markov kernel.

- *Equivariance.* Substituting $g=hg'$ and using left invariance of $\nu$
  gives $\bar\delta(hx)(hB)=\bar\delta(x)(B)$.
- *Risk formula.* By Tonelli, invariance of the loss
  ($L(\theta,ga)=L(g^{-1}\theta,a)$) and of the model
  ($g^{-1}$ maps $P_\theta$ to $P_{g^{-1}\theta}$),
  $$
  R(\theta,\bar\delta)=\int_GR(g^{-1}\theta,\delta)\,\nu(dg).
  $$
  A compact group is unimodular: for each $h$, the right translate
  $\nu\circ(\cdot\,h)^{-1}$ is a left-invariant probability measure, so it
  equals $\nu$ by uniqueness of Haar probability measures. Hence $\nu$ is
  inversion invariant, and the integral equals
  $\int_GR(g\theta,\delta)\,\nu(dg)$.
- *Consequences.* The average is at most $\sup_\theta R(\theta,\delta)$.
  So the infimum of the maximum risk over equivariant rules is at most the
  minimax value; the reverse inequality is trivial. Averaging a minimax
  rule gives an equivariant minimax rule.

**Library results.** `MeasureTheory.Measure.haarMeasure` in
`Mathlib/MeasureTheory/Measure/Haar/Basic.lean`;
`MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` in
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`;
`ProbabilityTheory.Kernel.compProd` in
`Mathlib/Probability/Kernel/Composition/CompProd.lean`;
`ProbabilityTheory.Kernel.const` in `Mathlib/Probability/Kernel/Basic.lean`;
`ProbabilityTheory.Kernel.map` in
`Mathlib/Probability/Kernel/Composition/MapComap.lean`.

### 101.47. Generalized Neyman–Pearson lemma

**Statement.** Let $f_0,f_1,\ldots,f_m$ be $\mu$-integrable real functions,
$k_1,\ldots,k_m$ real, and $\varphi_0$ a test equal to $1$ where
$f_0>\sum_ik_if_i$ and to $0$ where $f_0<\sum_ik_if_i$. Then $\varphi_0$
maximizes $\int\varphi f_0\,d\mu$ among tests that satisfy
$\int\varphi f_i\,d\mu\le\int\varphi_0f_i\,d\mu$ when $k_i>0$ and
$\int\varphi f_i\,d\mu\ge\int\varphi_0f_i\,d\mu$ when $k_i<0$. In
particular it maximizes among tests with equality for every $i$. Absent;
the proof is the pointwise argument of 101.14.

**Argument.** The function $(\varphi_0-\varphi)(f_0-\sum_ik_if_i)$ is
nonnegative pointwise and integrable, since tests are bounded. Integrating
it gives
$$
\int(\varphi_0-\varphi)f_0\,d\mu\ge\sum_ik_i\int(\varphi_0-\varphi)f_i\,d\mu\ge0,
$$
because each term of the sum is nonnegative under the sign constraints.
Indices with $k_i=0$ carry no constraint.

**Library results.** `MeasureTheory.integral_nonneg`,
`MeasureTheory.integral_sub` and `MeasureTheory.integral_finsetSum` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.

### 101.49. Neyman structure

**Statement.** If $T$ is boundedly complete and sufficient for
$\{P_\theta:\theta\in\omega\}$, then every $\alpha$-similar test on $\omega$
has Neyman structure with respect to $T$. So maximizing power among similar
tests reduces to maximizing conditional power given $T=t$ subject to
conditional size $\alpha$. Absent; it needs the notions of bounded
completeness and sufficiency.

**Scope.** The argument proves that every $\alpha$-similar test has Neyman
structure. The reduction in the second sentence follows by integrating the
pointwise inequality between conditional powers. That step needs the law of
$T$ under the alternative to be absolutely continuous with respect to its
law under the points of $\omega$, as it is in exponential families.

**Argument.** For $\theta\in\omega$, sufficiency gives
$\mathbb E_\theta[\varphi\mid T]=\psi(T)$ with
$\psi(t)=\int\varphi\,d\kappa(t)\in[0,1]$, free of $\theta$. Similarity
gives $\mathbb E_\theta(\psi(T)-\alpha)=\mathbb E_\theta\varphi-\alpha=0$
for every $\theta\in\omega$. The function $\psi-\alpha$ is bounded, so
bounded completeness gives $\psi(T)=\alpha$ almost surely under every
$\theta\in\omega$. This is Neyman structure.

**Library results.** `ProbabilityTheory.condExp_ae_eq_integral_condDistrib_id`
in `Mathlib/Probability/Kernel/CondDistrib.lean`;
`MeasureTheory.integral_condExp`.

### 101.53. Karlin–Rubin complete class theorem

**Statement.** Let a real-parameter family have monotone likelihood ratio in
$T$, and let the action space be $\{0,1\}$ (accept, reject). Let
$L(\theta,1)-L(\theta,0)$ be positive for $\theta<\theta_0$ and negative for
$\theta>\theta_0$. Then the one-sided tests, with $\varphi=1$ for $T>c$,
$\gamma$ at $T=c$ and $0$ for $T<c$, where $c\in[-\infty,\infty]$ and
$\gamma\in[0,1]$, form an essentially complete class: for every test there
is a one-sided test with risk no larger at every $\theta$. Absent from all
three libraries.

**Scope.** The argument covers every test $\varphi$ with
$0<\mathbb E_{\theta_0}\varphi<1$. Tests of size $0$ or $1$ at $\theta_0$
are covered by $\varphi'\equiv0$ or $\varphi'\equiv1$ when the laws are
mutually absolutely continuous. Without that assumption they need a
separate boundary argument, with $c$ the essential supremum or infimum of
$T$ under $\theta_0$.

**Argument.** The risk of a test is
$R(\theta,\varphi)=L(\theta,0)+(L(\theta,1)-L(\theta,0))\,\mathbb E_\theta\varphi$.
Let $a=\mathbb E_{\theta_0}\varphi\in(0,1)$. Choose $c$ and $\gamma$ with
$\mathbb E_{\theta_0}\varphi'=a$ for the one-sided test $\varphi'$, using
the quantile of the law of $T$ under $\theta_0$ as in 101.14.

- *For $\theta>\theta_0$.* The test $\varphi'$ has the Neyman–Pearson form
  for $\theta_0$ against $\theta$, with a finite constant because $a>0$.
  The optimality part of 101.14 gives
  $\mathbb E_\theta\varphi'\ge\mathbb E_\theta\varphi$.
- *For $\theta<\theta_0$.* The test $1-\varphi'$ has the Neyman–Pearson
  form for $\theta_0$ against $\theta$, since
  $f_\theta/f_{\theta_0}$ is nonincreasing in $T$; its constant is finite
  because $a<1$. Both $1-\varphi'$ and $1-\varphi$ have size $1-a$ at
  $\theta_0$, so $\mathbb E_\theta(1-\varphi')\ge\mathbb E_\theta(1-\varphi)$,
  that is $\mathbb E_\theta\varphi'\le\mathbb E_\theta\varphi$.

With the sign conditions on the loss, $R(\theta,\varphi')\le R(\theta,\varphi)$
for every $\theta$, with equality at $\theta_0$.

**Library results.** Those of 101.14.

### 101.54. Least favorable distributions

**Statement.** Let $\varphi_0$ be most powerful of level $\alpha$ for
$P_{\Lambda_0}$ against a simple alternative $Q$, and suppose
$\mathbb E_\vartheta\varphi_0\le\alpha$ for every $\vartheta\in\Theta_0$.
Then $\varphi_0$ is most powerful of level $\alpha$ for the composite null
against $Q$, and $\Lambda_0$ is least favorable: no other mixture $P_\Lambda$
gives a smaller most powerful power against $Q$. If the power of
$\varphi_0$ is below one, $\Lambda_0$ is concentrated on
$\{\vartheta:\mathbb E_\vartheta\varphi_0=\alpha\}$. Mathlib provides the
mixtures as compositions of a measure with a kernel;
the testing statement is absent.

**Argument.** For a test $\varphi$, the function
$\vartheta\mapsto\mathbb E_\vartheta\varphi$ is measurable, and
$\mathbb E_{P_\Lambda}\varphi=\int\mathbb E_\vartheta\varphi\,\Lambda(d\vartheta)$.

- *Most powerful for the composite null.* A test of level $\alpha$ for the
  composite null therefore has size at most $\alpha$ under $P_{\Lambda_0}$.
  Its power is then at most that of $\varphi_0$, and $\varphi_0$ itself has
  level $\alpha$ for the composite null.
- *Least favorable.* For any $\Lambda$, the test $\varphi_0$ has size at
  most $\alpha$ under $P_\Lambda$. So the most powerful power against
  $P_\Lambda$ is at least $\mathbb E_Q\varphi_0$, the most powerful power
  against $P_{\Lambda_0}$.
- *Concentration.* Suppose $\mathbb E_Q\varphi_0<1$ and
  $\mathbb E_{P_{\Lambda_0}}\varphi_0<\alpha$. For small $\varepsilon>0$
  the test $\varphi_0+\varepsilon(1-\varphi_0)$ has level $\alpha$ under
  $P_{\Lambda_0}$ and strictly larger power, a contradiction. So
  $\int\mathbb E_\vartheta\varphi_0\,\Lambda_0(d\vartheta)=\alpha$ with an
  integrand at most $\alpha$. The integrand equals $\alpha$
  $\Lambda_0$-almost everywhere, and the set where it does is measurable.

**Library results.** The mixture $P_\Lambda$ is the composition of $\Lambda$
with the kernel $\vartheta\mapsto P_\vartheta$, a
`MeasureTheory.Measure.bind`. Its integrals are given by
`MeasureTheory.Measure.lintegral_bind` in
`Mathlib/MeasureTheory/Measure/GiryMonad.lean`;
`MeasureTheory.integral_eq_zero_iff_of_nonneg`.

### 101.58. Blyth's method

**Statement.** Let $\Theta$ be a convex subset of Euclidean space with
nonempty interior. Let the rules with continuous risk form a complete
class, and let $\delta_0$ have continuous risk. Suppose there are finite,
possibly unnormalized, priors $\pi_n$ with Bayes rules $\delta_n$ such that
$r(\pi_n,\delta_0)$ and $r(\pi_n,\delta_n)$ are finite; for every convex
$C\subset\Theta$ with nonempty interior there are $K>0$ and $N$ with
$\pi_n(C)\ge K$ for $n\ge N$; and
$r(\pi_n,\delta_0)-r(\pi_n,\delta_n)\to0$. Then $\delta_0$ is admissible. For
$X\sim N(\theta,1)$, the priors
$e^{-\theta^2/(2n)}\,d\theta$ prove admissibility of $X$. Mathlib's Bayes
risk accepts unnormalized priors, but admissibility is not defined and the
theorem is absent.

**Scope.** The argument proves the general criterion. The normal example
remains a gap. It also needs the posterior computation and the fact that
rules with continuous risk form a complete class for the normal location
family.

**Argument.** Suppose $\delta_0$ is inadmissible, dominated by $\delta'$
with strict inequality at $\theta_1$. By the complete-class hypothesis
there is $\delta''$ with continuous risk and
$R(\cdot,\delta'')\le R(\cdot,\delta')$. Then $R(\theta_1,\delta_0)
-R(\theta_1,\delta'')=2\varepsilon>0$. By continuity this difference is at
least $\varepsilon$ on $C=B(\theta_1,\rho)\cap\Theta$ for some $\rho>0$.
The set $C$ is convex with nonempty interior: segments from $\theta_1$ to
an interior point of $\Theta$ lie in the interior except at $\theta_1$.
Since $\delta_n$ is Bayes for $\pi_n$,
$$
r(\pi_n,\delta_0)-r(\pi_n,\delta_n)\ge r(\pi_n,\delta_0)-r(\pi_n,\delta'')
=\int(R(\cdot,\delta_0)-R(\cdot,\delta''))\,d\pi_n\ge\varepsilon K
$$
for $n\ge N$. All terms are finite because
$r(\pi_n,\delta'')\le r(\pi_n,\delta_0)<\infty$. This contradicts the
convergence to zero.

**Library results.** `ProbabilityTheory.avgRisk` and
`ProbabilityTheory.bayesRisk_le_avgRisk` in
`Mathlib/Probability/Decision/Risk/Defs.lean` and
`Mathlib/Probability/Decision/Risk/Basic.lean`; monotonicity of the
lower Lebesgue integral.

### 101.60. Scheffé's method

**Statement.** Consider the normal linear model $Y=X\beta+\varepsilon$ with
$\varepsilon\sim N_n(0,\sigma^2I_n)$ and $X$ of rank $r<n$. Let $\hat\beta$
be a least-squares estimator, put
$\hat\sigma^2=\|Y-X\hat\beta\|^2/(n-r)$, and let $C$ be the column space of
$X^\top$. Then
$$\sup_{c\in C\setminus\{0\}}
\frac{(c\cdot(\hat\beta-\beta))^2}{\hat\sigma^2\,c^\top(X^\top X)^-c}
=\frac{(\hat\beta-\beta)^\top X^\top X(\hat\beta-\beta)}{\hat\sigma^2},$$
which has the law of $rF_{r,n-r}$. So the intervals
$c\cdot\hat\beta\pm\hat\sigma\sqrt{rF_{r,n-r,1-\alpha}\,c^\top(X^\top X)^-c}$,
$c\in C$, have exact simultaneous coverage $1-\alpha$. TauCeti has the $F$
law as a ratio of independent chi-squared laws, the moment generating
function of Gaussian quadratic forms, and the chi-squared laws and
independence of the projections of a standard Gaussian vector onto
mutually orthogonal subspaces, which is Cochran's theorem in projection
form. Missing are the identification of the fitted values and residuals of
a least-squares fit with such projections, the evaluation of the supremum
by Cauchy–Schwarz, and the coverage statement; with the projection
theorems these form a short argument.

**Argument.** Let $V$ be the column space of $X$, of dimension $r\ge1$, and
$P_V$ the orthogonal projection onto it.

- *Cochran.* The vector $\varepsilon/\sigma$ has the standard Gaussian law
  on $\mathbb R^n$. The subspaces $V$ and $V^\perp$ are orthogonal, of
  dimensions $r$ and $n-r$. TauCeti's projection theorem for a pair of
  orthogonal subspaces gives the joint law of
  $(\|P_V\varepsilon\|^2/\sigma^2,\|P_{V^\perp}\varepsilon\|^2/\sigma^2)$
  as the product of $\chi^2_r$ and $\chi^2_{n-r}$: the two are independent
  with these laws.
- *Least squares.* $X\hat\beta$ minimizes $\|Y-v\|$ over $v\in V$, so
  $X\hat\beta=P_VY$. Hence $X(\hat\beta-\beta)=P_V\varepsilon$ and
  $Y-X\hat\beta=P_{V^\perp}\varepsilon$.
- *Generalized inverse.* For any $G$ with $X^\top XGX^\top X=X^\top X$,
  $XGX^\top=P_V$. Indeed, with $D=XGX^\top X-X$ one computes $D^\top D=0$,
  using that $G^\top$ is also a generalized inverse. So $XGX^\top$ is the
  identity on $V$, and it vanishes on $V^\perp=\ker X^\top$.
- *The supremum.* Write $c=X^\top a$ and $u=P_Va$. Then $X^\top a=X^\top u$,
  so $c\ne0$ forces $u\ne0$. Moreover
  $c\cdot(\hat\beta-\beta)=\langle u,P_V\varepsilon\rangle$ and
  $c^\top Gc=\|u\|^2$. As $c$ ranges over $C\setminus\{0\}$, $u$ ranges
  over $V\setminus\{0\}$. Cauchy–Schwarz, with equality at
  $u=P_V\varepsilon$ when $P_V\varepsilon\ne0$, gives
  $$
  \sup_{u\in V\setminus\{0\}}\frac{\langle u,w\rangle^2}{\|u\|^2}=\|w\|^2,
  \qquad w=P_V\varepsilon=X(\hat\beta-\beta).
  $$
  The common value of the two sides is therefore
  $r\cdot(\|P_V\varepsilon\|^2/r)/(\|P_{V^\perp}\varepsilon\|^2/(n-r))$.
  By the ratio theorem it has the law of $rF_{r,n-r}$. The quantities
  $c\cdot\hat\beta$ for $c\in C$ do not depend on the choice of $\hat\beta$.
- *Coverage.* The $F$ law is the image of a beta law, which has a density,
  under a map injective on $(0,1)$, so it has no atoms. The quantile then
  gives exact probability $1-\alpha$.

**Library results.** `map_pi_eq_stdGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`;
`TauCeti.Probability.map_norm_sq_orthogonalProjectionOnto_stdGaussian_pi`
in `TauCeti/Probability/Distributions/Gaussian/Projection.lean`;
`Submodule.isOrtho_orthogonal_right` in
`Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`;
`Submodule.finrank_add_finrank_orthogonal` in
`Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`;
`TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared` in
`TauCeti/Probability/Distributions/FisherSnedecor/ChiSquared.lean`;
`Submodule.starProjection_minimal`,
`Submodule.eq_starProjection_of_mem_of_inner_eq_zero` and
`norm_sq_eq_add_norm_sq_starProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
`real_inner_mul_inner_self_le` in
`Mathlib/Analysis/InnerProductSpace/Basic.lean`;
`MeasureTheory.Measure.cdf_quantile'` in `TauCeti/Probability/Quantile.lean`;
`TauCeti.Probability.fisherSnedecorMeasure` in
`TauCeti/Probability/Distributions/FisherSnedecor/Basic.lean`.

### 101.64. Stein's identity and unbiased risk estimation

**Statement.** Let $X\sim N_p(\theta,\sigma^2I)$ with known $\sigma^2>0$. Let
$g:\mathbb R^p\to\mathbb R^p$ be weakly differentiable with
$\mathbb E\|g(X)\|^2<\infty$ and $\mathbb E|\partial_ig_i(X)|<\infty$. Then
$$\mathbb E[(X_i-\theta_i)g_i(X)]=\sigma^2\,\mathbb E\,\partial_ig_i(X),$$
so the squared-error risk of $X+g(X)$ is the expectation of
$p\sigma^2+\|g(X)\|^2+2\sigma^2\sum_i\partial_ig_i(X)$. TauCeti proves the
identity in dimension one: for $X\sim N(\mu,v)$, $v\ge0$, and $f$
differentiable everywhere with $(x-\mu)f(x)$ and $f'$ integrable,
$\mathbb E[(X-\mu)f(X)]=v\,\mathbb Ef'(X)$. Missing are the
$p$-dimensional form for weakly differentiable $g$ and the unbiased risk
estimate.

**Scope.** The argument covers $g$ whose coordinate $g_i$ is, for almost
every value of the other coordinates, locally absolutely continuous in
$x_i$. This includes everywhere-differentiable $g$ with the stated
integrability. The identification of weakly differentiable functions with
such functions is the ACL characterization of Sobolev functions. It is not
in the libraries and remains a gap. The James–Stein choice
$g(x)=-(p-2)x/\|x\|^2$ of 101.57, $p\ge3$, is covered directly: almost
every coordinate line misses the origin, and on such a line $g_i$ is
smooth.

**Argument.** *One dimension.* Let $Y\sim N(\theta,\sigma^2)$ with density
$\phi$. If $h$ is differentiable everywhere and $(Y-\theta)h(Y)$ and $h'(Y)$
are integrable, TauCeti's identity gives
$\mathbb E[(Y-\theta)h(Y)]=\sigma^2\,\mathbb Eh'(Y)$ directly. For $h$
only locally absolutely continuous with $\mathbb E|h'(Y)|<\infty$, the
identity follows from Mathlib's calculus. For $x>\theta$,
$$
\phi(x)=\int_x^\infty\frac{t-\theta}{\sigma^2}\phi(t)\,dt,
$$
and symmetrically for $x<\theta$. Substitute this into
$\int h'\phi\,dx$, use Tonelli on $|h'|$ to justify Fubini, and apply
$\int_\theta^th'=h(t)-h(\theta)$. The result is
$$
\mathbb E h'(Y)=\sigma^{-2}\,\mathbb E[(Y-\theta)(h(Y)-h(\theta))]
=\sigma^{-2}\,\mathbb E[(Y-\theta)h(Y)],
$$
since $\mathbb E(Y-\theta)=0$. The computation shows that
$(Y-\theta)h(Y)$ is integrable.

*Several dimensions.* The law of $X$ is a product of one-dimensional
Gaussians. Fubini over the coordinate $x_i$ and the others, together with
Tonelli for $\mathbb E|\partial_ig_i|<\infty$ and for
$\mathbb E|(X_i-\theta_i)g_i(X)|<\infty$, which follows from
$\mathbb E\|g(X)\|^2<\infty$ by Cauchy–Schwarz, applies the
one-dimensional identity on almost every line; for everywhere-differentiable
$g$ every line satisfies the differentiability hypothesis of TauCeti's
identity, and almost every line its integrability hypotheses.

*Risk.* Expanding
$\|X+g(X)-\theta\|^2$ and using $\mathbb E\|X-\theta\|^2=p\sigma^2$ gives
the risk formula. Cauchy–Schwarz and $\mathbb E\|g\|^2<\infty$ justify the
expansion.

**Library results.**
`TauCeti.Probability.integral_sub_mul_eq_mul_integral_deriv_gaussianReal`
in `TauCeti/Probability/Distributions/Gaussian/IntegrationByParts.lean`;
`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`;
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` and
`integral_Iic_of_hasDerivAt_of_tendsto` in
`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`;
`ProbabilityTheory.gaussianPDFReal` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`;
`MeasureTheory.integral_prod` and `integral_integral_swap` in
`Mathlib/MeasureTheory/Integral/Prod.lean`;
`MeasureTheory.measurePreserving_piEquivPiSubtypeProd` in
`Mathlib/MeasureTheory/Constructions/Pi.lean`;
`map_pi_eq_stdGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`.

## 102. Asymptotic, semiparametric, and robust statistics

### 102.1. Delta method

**Statement.** If $\sqrt n(T_n-\theta)\Rightarrow N(0,\Sigma)$ in
$\mathbb R^k$ and $g:\mathbb R^k\to\mathbb R^m$ is Borel measurable and
differentiable at $\theta$, then
$$
\sqrt n\bigl(g(T_n)-g(\theta)\bigr)\Rightarrow
N\bigl(0,Dg(\theta)\Sigma Dg(\theta)^\top\bigr),
$$
and $\sqrt n(g(T_n)-g(\theta))-Dg(\theta)\sqrt n(T_n-\theta)\to_P0$.
Mathlib has Slutsky's theorem, continuous mapping, transfer of limits under
$o_P(1)$ perturbations, and Fréchet derivatives with little-$o$ remainder.
TauCeti computes affine images of multivariate Gaussians. The theorem
follows by a short argument once one lemma is supplied: a deterministic
$o(\|h\|)$ remainder evaluated along an $O_P(n^{-1/2})$ sequence is
$o_P(n^{-1/2})$. No library has that lemma or stochastic order symbols.

**Argument.** Measurability of $g$ is needed for $g(T_n)$ to be a random
vector; differentiability at one point does not give it. Mathlib's
transfer lemma works on one probability space. This is no restriction:
convergence in distribution depends only on the laws, and the $T_n$ can be
realized on the product of their spaces.

Put $Y_n=\sqrt n(T_n-\theta)$, let $Z\sim N(0,\Sigma)$, and write
$R(h)=g(\theta+h)-g(\theta)-Dg(\theta)h$. The remainder lemma asserts
$\sqrt n\,R(T_n-\theta)\to_P0$. Fix $\eta,\varepsilon>0$. Choose $M$ with
$P(\|Z\|\ge M)<\varepsilon$; the set $\{\|z\|\ge M\}$ is closed, so the
portmanteau theorem gives $\limsup_nP(\|Y_n\|\ge M)<\varepsilon$. Choose
$\rho>0$ with $\|R(h)\|\le(\eta/M)\|h\|$ for $\|h\|\le\rho$, and take $n$
so large that $M/\sqrt n\le\rho$. On $\{\|Y_n\|<M\}$,
$$
\sqrt n\,\|R(T_n-\theta)\|\le\frac\eta M\,\|Y_n\|<\eta .
$$
Hence $\limsup_nP(\sqrt n\|R(T_n-\theta)\|\ge\eta)\le\varepsilon$, which
proves the lemma and the second assertion.

Continuous mapping gives $Dg(\theta)Y_n\Rightarrow Dg(\theta)Z$. The
transfer lemma then gives the same limit for
$\sqrt n(g(T_n)-g(\theta))=Dg(\theta)Y_n+\sqrt nR(T_n-\theta)$. TauCeti's
affine-image formula identifies the law of $Dg(\theta)Z$ as
$N(0,Dg(\theta)\Sigma Dg(\theta)^\top)$.

**Library results.** `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`
in `Mathlib/MeasureTheory/Measure/Portmanteau.lean`;
`TendstoInDistribution.continuous_comp` and
`tendstoInDistribution_of_tendstoInMeasure_sub` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`;
`hasFDerivAt_iff_isLittleO_nhds_zero` in
`Mathlib/Analysis/Calculus/FDeriv/Basic.lean`;
`TauCeti.Probability.map_affine_multivariateGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Affine.lean`;
`MeasureTheory.Measure.infinitePi` in
`Mathlib/Probability/ProductMeasure.lean`.

### 102.8. Nondegenerate $U$-statistics

**Statement.** Let $h$ be a symmetric kernel of order $m$ with
$\mathbb Eh(X_1,\ldots,X_m)^2<\infty$, let $U_n$ be its average over the
$\binom nm$ subsamples, and put $\theta=\mathbb Eh$ and
$g(x)=\mathbb Eh(x,X_2,\ldots,X_m)-\theta$. If
$\zeta_1=\mathop{\mathrm{Var}}g(X_1)>0$, then
$\sqrt n(U_n-\theta)\Rightarrow N(0,m^2\zeta_1)$ and
$\sqrt n(U_n-\theta-n^{-1}\sum_img(X_i))\to0$ in $L^2$. Mathlib's $L^2$
conditional expectation supplies the projection operation; $U$-statistics
are not defined.

**Argument.** The argument is a finite covariance computation followed by
the central limit theorem. The hypothesis $\zeta_1>0$ is not needed: when
$\zeta_1=0$ the limit is the point mass at $0$.

For an $m$-subset $S$ write $h_S=h(X_S)$. Put
$\hat U_n=\theta+(m/n)\sum_ig(X_i)$ and
$\zeta_c=\mathop{\mathrm{Cov}}(h_S,h_{S'})$ for $|S\cap S'|=c$. The joint
law of the variables indexed by $S\cup S'$ is a product measure, and Fubini
over the blocks $S\cap S'$, $S\setminus S'$ and $S'\setminus S$ gives:

- $\zeta_0=0$, and $|\zeta_c|\le\mathbb Eh^2$ for every $c$;
- $\zeta_1=\mathop{\mathrm{Var}}g(X_1)$, since for $S\cap S'=\{i\}$,
  $\mathbb E[h_Sh_{S'}]=\int(g+\theta)^2\,dP$;
- $\mathop{\mathrm{Cov}}(h_S,g(X_i))=\zeta_1$ if $i\in S$ and $0$
  otherwise. Symmetry of $h$ makes this independent of the position of $i$
  in $S$.

Counting pairs of subsets then gives
$$
\mathop{\mathrm{Var}}U_n=\binom nm^{-1}\sum_{c=1}^m\binom mc\binom{n-m}{m-c}\zeta_c,
\qquad
\mathop{\mathrm{Cov}}(U_n,\hat U_n)=\mathop{\mathrm{Var}}\hat U_n=\frac{m^2\zeta_1}n .
$$
Hence $\mathbb E(U_n-\hat U_n)^2=\mathop{\mathrm{Var}}U_n-m^2\zeta_1/n$.
The $c=1$ coefficient is
$$
m\binom{n-m}{m-1}\binom nm^{-1}=\frac{m^2}n\prod_{j=1}^{m-1}\frac{n-m-j+1}{n-j}
=\frac{m^2}n+O(n^{-2}),
$$
and the terms with $c\ge2$ are $O(n^{-2})$. So
$n\,\mathbb E(U_n-\hat U_n)^2=O(n^{-1})\to0$, which is the $L^2$ statement.
The central limit theorem gives
$(\sqrt n)^{-1}\sum_ig(X_i)\Rightarrow N(0,\zeta_1)$. Multiplying by $m$
and transferring along the $L^2$-small difference gives the limit law.

**Library results.** `ProbabilityTheory.iIndepFun.hasLaw_pi` in
`Mathlib/Probability/HasLaw.lean`; `MeasureTheory.integral_prod` in
`Mathlib/MeasureTheory/Integral/Prod.lean`;
`ProbabilityTheory.IndepFun.covariance_eq_zero` in
`Mathlib/Probability/Moments/Covariance.lean`;
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` in
`Mathlib/Probability/CentralLimitTheorem.lean`;
`MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` in
`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`;
`TendstoInDistribution.continuous_comp` and
`tendstoInDistribution_of_tendstoInMeasure_sub` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`.

### 102.12. Contiguity

**Statement.** If the likelihood ratio $L_n=dQ_n^{\mathrm a}/dP_n$ of the
part of $Q_n$ absolutely continuous with respect to $P_n$ converges in
distribution under $P_n$ to $e^\Lambda$ for a real random variable $\Lambda$
with $\mathbb Ee^\Lambda=1$, then $Q_n$ is contiguous to $P_n$. In particular,
local alternatives in a LAN experiment are mutually contiguous. Mathlib has
absolute continuity, Radon–Nikodým derivatives, the Lebesgue decomposition
and log-likelihood ratios. Statlib defines contiguity for families of
probability measures indexed along a filter, in five formulations, among
them the one above and the condition that weak limits of the laws of
$dQ_n/dP_n$ under $P_n$ have mean one. It proves only that the set
formulation, tested along every finer filter, is equivalent to
preservation of convergence in probability and implies the set
formulation along the filter itself. The likelihood-ratio
characterizations, which contain this statement, appear there only as
plans in comments. With the definition in place the statement follows by a
short argument.

**Argument.** Statlib's set formulation `Contiguous1`, for sequences
indexed along the filter `Filter.atTop` of $\mathbb N$, is the definition
of contiguity used here. It requires $Q_n(A_n)\to0$ along every finer
filter along which $P_n(A_n)\to0$. The argument below applies verbatim
along any finer filter, since the convergence in distribution in the
hypothesis passes to finer filters. Its density $dQ_n/dP_n$ is Mathlib's Radon–Nikodým derivative,
which is the density $L_n$ of the absolutely continuous part in the
Lebesgue decomposition $Q_n=L_n\cdot P_n+Q_n^\perp$, where $Q_n^\perp$ is
singular to $P_n$. Mathlib's `llr` takes $\log0=0$, so the argument works,
as the statement does, with $L_n$ rather than with $\Lambda_n$.

*$Q_n$ is contiguous to $P_n$.* Let $P_n(A_n)\to0$ and fix $M>0$. Since
$Q_n^\perp(\Omega_n)=1-\int L_n\,dP_n$,
$$
Q_n(A_n)\le Q_n^\perp(\Omega_n)+\int_{A_n}\min(L_n,M)\,dP_n
+\int(L_n-\min(L_n,M))\,dP_n
\le MP_n(A_n)+1-\int\min(L_n,M)\,dP_n .
$$
The function $\min(e^\lambda,M)$ is bounded and continuous, so
$\int\min(L_n,M)\,dP_n\to\mathbb E\min(e^\Lambda,M)$. Hence
$\limsup_nQ_n(A_n)\le1-\mathbb E\min(e^\Lambda,M)$, which tends to
$1-\mathbb Ee^\Lambda=0$ as $M\to\infty$ by monotone convergence.

*$P_n$ is contiguous to $Q_n$.* This direction needs only that $\Lambda$
is real-valued. If $Q_n(A_n)\to0$, then for $\varepsilon>0$,
$$
P_n(A_n)\le\varepsilon^{-1}\int_{A_n}L_n\,dP_n+P_n(L_n\le\varepsilon)
\le\varepsilon^{-1}Q_n(A_n)+P_n(L_n\le\varepsilon).
$$
By the portmanteau theorem for the closed set $\{x\le\varepsilon\}$,
$\limsup_nP_n(L_n\le\varepsilon)\le P(e^\Lambda\le\varepsilon)$. This
tends to $P(e^\Lambda=0)=0$ as $\varepsilon\downarrow0$.

*LAN.* In a LAN experiment, $h\cdot\Delta_n\Rightarrow N(0,\sigma^2)$ with
$\sigma^2=h^\top I(\theta)h$. Adding the constant $-\sigma^2/2$ and the
$o_P(1)$ term gives $\Lambda_n\Rightarrow\Lambda\sim N(-\sigma^2/2,\sigma^2)$,
and the Gaussian moment generating function gives $\mathbb Ee^\Lambda=1$.
Both contiguity relations follow. For the $o_P(1)$ transfer, Mathlib's
lemma needs one probability space; for independent sampling the product
experiments are realized on the infinite product $X^{\mathbb N}$.

**Library results.** `Contiguous1` in `Statlib/Contiguity/Def.lean`;
`MeasureTheory.Measure.rnDeriv_add_singularPart` in
`Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean`;
`MeasureTheory.Measure.setLIntegral_rnDeriv_le` in
`Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`;
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` in
`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`;
`MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` in
`Mathlib/MeasureTheory/Measure/Portmanteau.lean`;
`MeasureTheory.lintegral_iSup` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`;
`ProbabilityTheory.mgf_gaussianReal` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`;
`tendstoInDistribution_of_tendstoInMeasure_sub` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`;
`MeasureTheory.Measure.infinitePi` in
`Mathlib/Probability/ProductMeasure.lean`.

### 102.23. Consistency of $M$-estimators

**Statement.** Suppose $\sup_\theta|P_nm_\theta-Pm_\theta|\to_P0$ and
$\sup_{d(\theta,\theta_0)\ge\varepsilon}Pm_\theta<Pm_{\theta_0}$ for every
$\varepsilon>0$. If $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(1)$,
then $\hat\theta_n\to_P\theta_0$. The uniform convergence holds when
$\Theta$ is a compact metric space, $\theta\mapsto m_\theta(x)$ is
continuous, and $P\sup_\theta|m_\theta|<\infty$. TauCeti proves almost-sure
consistency of empirical Fréchet barycenters in separable metric spaces, an
$M$-estimator with criterion $-d(\theta,x)^p$, by way of Wasserstein
convergence of empirical measures. Missing are the general criterion and
the uniform law of large numbers over a compact parameter set.

**Argument.** The statement presupposes that $\hat\theta_n$ is measurable
and that the supremum is a random variable. Under the continuity
hypothesis, measurability of suprema is automatic: a supremum over $\Theta$
or over a ball equals the supremum over a countable dense subset.

*Criterion.* Fix $\varepsilon>0$ and put
$\eta=Pm_{\theta_0}-\sup_{d(\theta,\theta_0)\ge\varepsilon}Pm_\theta>0$.
Write $D_n=\sup_\theta|P_nm_\theta-Pm_\theta|$ and
$R_n=\sup_\theta P_nm_\theta-P_nm_{\hat\theta_n}$, so $R_n\to_P0$. On
$\{d(\hat\theta_n,\theta_0)\ge\varepsilon\}$,
$$
\eta\le Pm_{\theta_0}-Pm_{\hat\theta_n}
\le(Pm_{\theta_0}-P_nm_{\theta_0})+(P_nm_{\theta_0}-P_nm_{\hat\theta_n})
+(P_nm_{\hat\theta_n}-Pm_{\hat\theta_n})\le2D_n+R_n .
$$
So $P(d(\hat\theta_n,\theta_0)\ge\varepsilon)\le P(2D_n+R_n\ge\eta)\to0$.

*Uniform law of large numbers.* For $\theta\in\Theta$ and $\delta>0$ let
$u_{\theta,\delta}$ and $l_{\theta,\delta}$ be the supremum and infimum of
$m_{\theta'}$ over $d(\theta',\theta)<\delta$. Both are dominated by the
integrable envelope. By continuity, $u_{\theta,\delta}-l_{\theta,\delta}\to0$
pointwise as $\delta\to0$, so dominated convergence makes
$P(u_{\theta,\delta}-l_{\theta,\delta})<\varepsilon$ for small $\delta$.
Compactness gives finitely many balls $B(\theta_j,\delta_j)$ covering
$\Theta$. For $\theta$ in the $j$th ball,
$$
P_nl_j-Pl_j-\varepsilon\le P_nm_\theta-Pm_\theta\le P_nu_j-Pu_j+\varepsilon .
$$
The strong law for the finitely many integrable $u_j,l_j$ gives
$\limsup_nD_n\le\varepsilon$ almost surely. Almost-sure convergence
implies convergence in probability.

**Library results.** `ProbabilityTheory.strong_law_ae_real` in
`Mathlib/Probability/StrongLaw.lean`;
`MeasureTheory.tendstoInMeasure_of_tendsto_ae` in
`Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean`;
`MeasureTheory.tendsto_integral_of_dominated_convergence` in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`;
`IsCompact.elim_finite_subcover` in
`Mathlib/Topology/Compactness/Compact.lean`.

### 102.31. Pearson's multinomial tests

**Statement.** Let $(N_1,\ldots,N_k)\sim\mathop{\mathrm{Mult}}(n;p)$ with
fixed $k$ and all $p_i>0$. Then $\sum_i(N_i-np_i)^2/(np_i)\Rightarrow\chi^2_{k-1}$.
Next let $p=p(\vartheta_0)$ for a map $\vartheta\mapsto p(\vartheta)$ from
an open set in $\mathbb R^d$ into the open simplex that is continuously
differentiable with derivative of rank $d$ at $\vartheta_0$. If
$\hat\vartheta_n$ is a consistent maximum likelihood estimator of
$\vartheta_0$, the statistic with $p(\hat\vartheta_n)$ in place of $p$
converges to $\chi^2_{k-1-d}$. For an $r\times c$ table under
independence, fitted counts $\hat N_{ij}=N_{i+}N_{+j}/n$ give
$(r-1)(c-1)$ degrees of freedom. The likelihood-ratio statistic
$2\sum N_{ij}\log(N_{ij}/\hat N_{ij})$, with $0\log0=0$, has the same limit
and differs from Pearson's by $o_P(1)$. TauCeti computes the multinomial
covariance and proves the chi-squared law of the squared norm of a
standard Gaussian vector after an orthogonal projection of rank $k-1$. The
simple-hypothesis case follows by a short argument from these and the
multivariate central limit theorem, which is not stated but follows from
Mathlib's Cramér–Wold device and one-dimensional central limit theorem;
the composite case needs 102.3.

**Scope.** The argument proves the simple-hypothesis case, the first
sentence. The composite and contingency-table statements, and the
likelihood-ratio comparison, remain gaps.

**Argument.** The statement concerns only laws, so realize $N$ as
$\sum_{l<n}\xi_l$, with $\xi_l$ independent copies of the indicator vector
$e_J$ for $J$ drawn from $p$. Put $u=(\sqrt{p_1},\ldots,\sqrt{p_k})$, a
unit vector, and $Y_l=((\xi_{l,i}-p_i)/\sqrt{p_i})_i$. A finite computation
gives
$$
\mathop{\mathrm{Var}}\langle t,Y_l\rangle=\|t\|^2-\langle t,u\rangle^2
=\|(I-uu^\top)t\|^2 .
$$

*Multivariate limit.* Let $G$ be standard Gaussian on $\mathbb R^k$ and
$W=G-\langle G,u\rangle u$. Then $\langle t,W\rangle=\langle(I-uu^\top)t,G\rangle$
has the law $N(0,\|(I-uu^\top)t\|^2)$. For each $t$, the one-dimensional
central limit theorem gives
$\langle t,Z_n\rangle\Rightarrow\langle t,W\rangle$ for
$Z_n=n^{-1/2}\sum_{l<n}Y_l$. The Cramér–Wold theorem gives
$Z_n\Rightarrow W$.

*Chi-squared limit.* The statistic is $\|Z_n\|^2$, so continuous mapping
gives $\|Z_n\|^2\Rightarrow\|W\|^2$. The vector $W$ is the orthogonal
projection of $G$ onto the complement $K$ of the line spanned by $u$,
which has dimension $k-1$. TauCeti's projection theorem gives
$\|W\|^2\sim\chi^2_{k-1}$. For $k=1$ both sides are the point mass at $0$;
TauCeti's theorem includes the zero subspace.

**Library results.** `ProbabilityTheory.exists_iid` in
`Mathlib/Probability/HasLawExists.lean`;
`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub` in
`Mathlib/Probability/CentralLimitTheorem.lean`;
`tendstoInDistribution_iff_tendstoInDistribution_inner` in
`Mathlib/Probability/CramerWold.lean`;
`TendstoInDistribution.continuous_comp` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`;
`Submodule.map_norm_sq_starProjection_stdGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Projection.lean`;
`Submodule.starProjection_orthogonal_val` and
`Submodule.starProjection_singleton` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
`Submodule.finrank_orthogonal_span_singleton` in
`Mathlib/Analysis/InnerProductSpace/Projection/FiniteDimensional.lean`;
`ProbabilityTheory.charFun_stdGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`, for the
law of $\langle t,W\rangle$.

### 102.44. $M$-estimators and the Huber minimax property

**Statement.** For odd continuous $\psi$, let $T$ be the location
$M$-functional defined by $\int\psi(x-T(G))\,dG(x)=0$ on a set of laws
containing the contaminations $(1-\varepsilon)F+\varepsilon\delta_x$. Put
$\theta_0=T(F)$ and $\lambda(\theta)=\int\psi(x-\theta)\,dF$. Assume
$\lambda$ is differentiable at $\theta_0$ with
$\gamma=-\lambda'(\theta_0)\ne0$, and that
$\varepsilon\mapsto T((1-\varepsilon)F+\varepsilon\delta_x)$ is
differentiable at $0$. Then
$\mathop{\mathrm{IF}}(x;T,F)=\psi(x-\theta_0)/\gamma$. If moreover $\psi$
is Lipschitz and $\mathbb E\psi(X-\theta_0)^2<\infty$, a consistent
sequence $\hat\theta_n$ with $\sum_i\psi(X_i-\hat\theta_n)=o_P(n^{1/2})$
satisfies
$\sqrt n(\hat\theta_n-\theta_0)\Rightarrow
N(0,\mathbb E\psi(X-\theta_0)^2/\gamma^2)$.

Hampel's optimality: for $c>\sqrt{\pi/2}$, among $\phi$ with
$\int\phi\,d\Phi=0$, $\int x\phi\,d\Phi=1$ and $\sup|\phi|\le c$, the
integral $\int\phi^2d\Phi$ is uniquely minimized by $\psi_k/(2\Phi(k)-1)$,
where $k/(2\Phi(k)-1)=c$.

Huber's minimax property: for $0<\varepsilon<1$ let $k$ solve
$2\varphi(k)/k-2\Phi(-k)=\varepsilon/(1-\varepsilon)$. Let $G_0$ have
density $(1-\varepsilon)\varphi(x)$ for $|x|\le k$ and
$(1-\varepsilon)\varphi(k)e^{k^2-k|x|}$ for $|x|>k$. Then
$G_0=(1-\varepsilon)\Phi+\varepsilon H_0$ with $H_0$ symmetric, and
$\psi_k=-g_0'/g_0$. With $V(\psi_k,G)=\int\psi_k^2\,dG/G((-k,k))^2$,
$$V(\psi_k,G)\le V(\psi_k,G_0)=1/I(G_0)$$
for every $G=(1-\varepsilon)\Phi+\varepsilon H$ with symmetric $H$, while
$\int\psi^2dG_0/(\int\psi'dG_0)^2\ge1/I(G_0)$ for every bounded absolutely
continuous $\psi$ with $\int\psi'dG_0\ne0$.

TauCeti supplies $\Phi$ and $\varphi$ as real functions. Influence
functions and the variance functional are not defined, and Mathlib's Sion
theorem does not apply directly to Huber's saddle point.

**Scope.** The argument proves the influence-function formula, Hampel's
optimality, and all assertions of Huber's minimax property. The
asymptotic normality of $\hat\theta_n$ is a $Z$-estimator theorem
(compare 102.4) and remains a gap.

**Argument.** *Influence function.* Write
$T_\varepsilon=T((1-\varepsilon)F+\varepsilon\delta_x)$, so that
$$
(1-\varepsilon)\lambda(T_\varepsilon)+\varepsilon\psi(x-T_\varepsilon)=0
\qquad(0\le\varepsilon<1).
$$
Differentiate from the right at $\varepsilon=0$. The chain rule applies to
$\lambda(T_\varepsilon)$ because $\lambda$ is differentiable at
$T_0=\theta_0$. The factor $\psi(x-T_\varepsilon)$ is continuous at $0$.
Using $\lambda(\theta_0)=0$ this gives
$-\gamma\,T'_0+\psi(x-\theta_0)=0$. Oddness of $\psi$ is not used.

*Hampel.* Put $a=1/(2\Phi(k)-1)$, so $c=ak$ and
$\psi^*=a\psi_k=\max(-c,\min(c,ax))$. For an admissible $\phi$,
$$
\int\phi^2\,d\Phi=\int(\phi-ax)^2\,d\Phi+2a-a^2 .
$$
Pointwise, $|\phi(x)-ax|\ge|\psi^*(x)-ax|$ when $|\phi|\le c$, with
equality only if $\phi(x)=\psi^*(x)$. So $\psi^*$ is the unique minimizer
up to $\Phi$-null sets, provided it is admissible. It is odd, so
$\int\psi^*d\Phi=0$. Integration by parts gives
$\int_{-k}^kx^2\varphi=2\Phi(k)-1-2k\varphi(k)$, and
$\int_k^\infty x\varphi=\varphi(k)$. Hence
$\int x\psi_k\,d\Phi=2\Phi(k)-1$ and $\int x\psi^*d\Phi=1$. A suitable $k$
exists by the intermediate value theorem. The continuous function
$k/(2\Phi(k)-1)$ on $(0,\infty)$ tends to $1/(2\varphi(0))=\sqrt{\pi/2}$ as
$k\downarrow0$, by the derivative of $\Phi$ at $0$, and to $\infty$ as
$k\to\infty$.

*Huber.*

- *Decomposition.* The total mass of $G_0$ is
  $(1-\varepsilon)(2\Phi(k)-1+2\varphi(k)/k)$, which equals $1$ exactly by
  the equation for $k$. Also $g_0\ge(1-\varepsilon)\varphi$, because
  $k^2-k|x|\ge(k^2-x^2)/2$. So $H_0=(G_0-(1-\varepsilon)\Phi)/\varepsilon$
  is a symmetric probability measure carried by $\{|x|\ge k\}$.
- *Score.* Off $\{\pm k\}$, $-g_0'/g_0$ equals $x$ for $|x|<k$ and
  $k\mathop{\mathrm{sign}}x$ for $|x|>k$, which is $\psi_k$.
- *Upper bound.* Since $\psi_k^2\le k^2$,
  $\int\psi_k^2dG\le(1-\varepsilon)\int\psi_k^2d\Phi+\varepsilon k^2$. Also
  $G((-k,k))\ge(1-\varepsilon)\Phi((-k,k))$. Both hold with equality for
  $H_0$, so $V(\psi_k,G)\le V(\psi_k,G_0)$. Symmetry of $H$ is not needed.
- *Value at $G_0$.* The integrals above give
  $I(G_0)=\int\psi_k^2dG_0=(1-\varepsilon)(2\Phi(k)-1)=G_0((-k,k))$, so
  $V(\psi_k,G_0)=1/I(G_0)$.
- *Lower bound.* On $[-R,R]$, integrate by parts for the absolutely
  continuous $\psi$ and the Lipschitz $g_0$, and let $R\to\infty$; the
  boundary terms vanish because $\psi$ is bounded and $g_0\to0$. This
  gives $\int\psi'dG_0=\int\psi\psi_k\,dG_0$, where $\psi'g_0$ is assumed
  integrable. Cauchy–Schwarz gives
  $(\int\psi'dG_0)^2\le\int\psi^2dG_0\cdot I(G_0)$.

**Library results.** `HasDerivWithinAt.comp` in
`Mathlib/Analysis/Calculus/Deriv/Comp.lean` and `HasDerivWithinAt.mul` in
`Mathlib/Analysis/Calculus/Deriv/Mul.lean`;
`TauCeti.Probability.cdf_gaussianReal_eq` and
`TauCeti.Probability.hasDerivAt_cdf_gaussianReal` in
`TauCeti/Probability/Distributions/Gaussian/Cdf.lean`;
`ProbabilityTheory.gaussianPDFReal` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`;
`intervalIntegral.integral_mul_deriv_eq_deriv_mul` in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean`;
`MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` in
`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`;
`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` in
`Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`;
`LipschitzOnWith.absolutelyContinuousOnInterval` in
`Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`;
`intermediate_value_Ioo` in `Mathlib/Topology/Order/IntermediateValue.lean`;
`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` (with $p=q=2$) in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.

## 103. Nonparametric and high-dimensional inference

### 103.1. Kolmogorov–Smirnov statistic

**Statement.** If $F$ is continuous, the law of $\sup_x|F_n(x)-F(x)|$ does
not depend on $F$, and as $n\to\infty$
$$\sqrt n\sup_x|F_n(x)-F(x)|\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,\qquad
P\bigl(\sup_t|B^0(t)|\le x\bigr)
=1-2\sum_{k=1}^\infty(-1)^{k-1}e^{-2k^2x^2}\quad(x>0).$$
For every $n$ and every $x>0$ (Dvoretzky–Kiefer–Wolfowitz, with Massart's
constant), $P\bigl(\sqrt n\sup_x|F_n(x)-F(x)|>x\bigr)\le2e^{-2x^2}$. TauCeti
proves the probability integral transform for atomless laws and quantile
sampling for every law on the line, from which the distribution-freeness
follows by a short reduction to uniform samples that is not stated. Mathlib
defines Brownian motion through its finite-dimensional laws; missing are the
Brownian bridge, weak convergence in $\ell^\infty$, Donsker's theorem, the
Kolmogorov distribution, and the inequality.

**Scope.** Only the distribution-freeness of $D_n=\sup_x|F_n(x)-F(x)|$ for
continuous $F$. The limit law, the Kolmogorov series, and the
Dvoretzky–Kiefer–Wolfowitz–Massart inequality remain substantial gaps.

**Argument.** Let $Q$ be the quantile function of the law of $X_1$ and
$U_1,\ldots,U_n$ independent uniform on $(0,1)$. Quantile sampling gives
$Q_\ast(\mathrm{Unif}(0,1))=\mathrm{Law}(X_1)$, and pushing forward the
product measure coordinatewise gives
$\mathrm{Law}(X_1,\ldots,X_n)=\mathrm{Law}(Q(U_1),\ldots,Q(U_n))$. It
therefore suffices to compute $D_n$ for the sample $Q(U_i)$. For
$0<u<1$, $Q(u)\le x$ if and only if $u\le F(x)$, so
$$F_n(x)=\frac1n\#\{i:Q(U_i)\le x\}=G_n(F(x)),\qquad
G_n(t)=\frac1n\#\{i:U_i\le t\}.$$
Hence $D_n=\sup_{t\in F(\mathbb R)}|G_n(t)-t|$. Since $F$ is continuous with
limits $0$ and $1$, the intermediate value theorem gives
$(0,1)\subset F(\mathbb R)\subset[0,1]$. At $t=0$ and $t=1$ the difference
$G_n(t)-t$ vanishes because every $U_i$ lies in $(0,1)$. Thus
$D_n=\sup_{0<t<1}|G_n(t)-t|$, a function of the uniform sample alone, whose
law depends only on $n$. Measurability: $F_n-F$ is right-continuous, so the
supremum over $\mathbb R$ equals the supremum over $\mathbb Q$.

**Library results.** `MeasureTheory.Measure.map_quantile_volume_Ioo` and
`MeasureTheory.Measure.quantile_le_iff` in TauCeti's
`TauCeti/Probability/Quantile.lean`; `MeasureTheory.Measure.pi_map_pi` in
`Mathlib/MeasureTheory/Constructions/Pi.lean`; `ProbabilityTheory.cdf` and
its continuity and limits in `Mathlib/Probability/CDF.lean`.

### 103.8. Representer theorem

**Statement.** Let $\mathcal H$ be a reproducing-kernel Hilbert space of real
functions on $\mathcal X$ with kernel $K$, and let the loss $L(y,u)$ depend on
$f$ only through $u=f(X_i)$. A minimizer of
$$\frac1n\sum_{i=1}^nL(Y_i,f(X_i))+\lambda\|f\|_{\mathcal H}^2,
\qquad\lambda>0,$$
over $f\in\mathcal H$ has the form $f=\sum_{i=1}^n\alpha_iK(X_i,\cdot)$. In
particular, for $n\ge2$ distinct design points in $[a,b]$, the criterion
$\sum_i(Y_i-f(x_i))^2+\lambda\int_a^b(f'')^2$ on the Sobolev space of
functions with square-integrable second derivative has a minimizer that is a
natural cubic spline with knots at the design points. No penalized criterion
is formalized, and the spline case needs Sobolev functions on an interval and
the characterization of natural cubic splines, which are absent.

**Scope.** The general reproducing-kernel statement. The cubic-spline case
remains a gap: it needs the Sobolev space on $[a,b]$, its reproducing kernel
for the seminorm $\int(f'')^2$ with the null space of linear functions, and
the characterization of natural cubic splines.

**Argument.** Fix the data and let $\hat f$ be a minimizer. The subspace
$S=\mathop{\mathrm{span}}\{K(X_1,\cdot),\ldots,K(X_n,\cdot)\}$ is finite
dimensional, hence complete, so the orthogonal projection onto $S$ exists.
Write $\hat f=f_\parallel+f_\perp$ with $f_\parallel\in S$ and
$f_\perp\perp S$. In Mathlib's formulation the kernel function at $x$ is
$k_x=\mathrm{kerFun}\,x\,1$, and the reproducing property gives
$f(x)=\langle f,k_x\rangle$. Hence $f_\perp(X_i)=\langle f_\perp,
k_{X_i}\rangle=0$ and $\hat f(X_i)=f_\parallel(X_i)$, so the loss term is the
same for $\hat f$ and $f_\parallel$. Pythagoras gives
$\|\hat f\|^2=\|f_\parallel\|^2+\|f_\perp\|^2$. If $f_\perp\ne0$, then
$f_\parallel$ has strictly smaller criterion because $\lambda>0$,
contradicting minimality. So $\hat f=f_\parallel\in S$. No convexity of $L$
is used and existence of a minimizer is not claimed. If the $X_i$ repeat,
the representation has repeated terms, which is harmless.

**Library results.** `RKHS`, `RKHS.kerFun`, `RKHS.inner_kerFun` in
`Mathlib/Analysis/InnerProductSpace/Reproducing.lean`;
`Submodule.HasOrthogonalProjection.ofCompleteSpace`,
`Submodule.starProjection_add_starProjection_orthogonal` and
`Submodule.norm_sq_eq_add_norm_sq_starProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`; completeness of
finite-dimensional spaces (`FiniteDimensional.complete` in
`Mathlib/Topology/Algebra/Module/FiniteDimension.lean`).

### 103.17. Cramér–von Mises and two-sample Kolmogorov–Smirnov limits

**Statement.** If $F$ is continuous, $W_n^2=n\int(F_n-F)^2\,dF$ is
distribution-free and
$$W_n^2\Rightarrow\int_0^1B^0(t)^2\,dt
\stackrel{d}{=}\sum_{j=1}^\infty\frac{Z_j^2}{j^2\pi^2}$$
with $Z_j$ independent standard normal. For independent samples of sizes
$m,n$ with empirical distribution functions $F_m,G_n$ from a common
continuous law, $D_{m,n}=\sup_x|F_m(x)-G_n(x)|$ is distribution-free and
$\sqrt{mn/(m+n)}\,D_{m,n}\Rightarrow\sup_t|B^0(t)|$ as
$\min(m,n)\to\infty$; under differing laws the normalized statistic tends to
infinity in probability. For a parametric family with
$\sup_x|F_{\theta+u}(x)-F_\theta(x)-u^\top\dot F_\theta(x)|=o(|u|)$ and an
asymptotically linear estimator, $\sqrt n(F_n-F_{\hat\theta_n})$ converges in
law in $\ell^\infty(\mathbb R)$ to a centered Gaussian process $G$ with the
covariance given in `GAPS.md`, and
$\sqrt n\sup_x|F_n-F_{\hat\theta_n}|\Rightarrow\sup_x|G(x)|$. The libraries
supply only the ingredients listed under 103.1; the Karhunen–Loève expansion
of the bridge and all three limit theorems are missing.

**Scope.** The distribution-freeness of $W_n^2$ and of $D_{m,n}$, and the
divergence of $\sqrt{mn/(m+n)}\,D_{m,n}$ under differing laws. The three
limit laws, the series representation, and the estimated-parameter process
remain substantial gaps.

**Argument.** As in 103.1, represent $X_i=Q(U_i)$ with independent uniform
$U_i$, so that $F_n=G_n\circ F$ with $G_n$ the uniform empirical
distribution function. Then
$$W_n^2=n\int(G_n(F(x))-F(x))^2\,dF(x)=n\int_0^1(G_n(t)-t)^2\,dt,$$
by the change of variables formula for the image of $\mathrm{Law}(X_1)$
under $F$, which is the uniform law on $[0,1]$ because $F$ is continuous.
The right side is a function of the uniform sample only. For the two-sample
statistic represent both samples through the common quantile function:
$F_m=G_m\circ F$ and $G_n=H_n\circ F$ with independent uniform empirical
distribution functions $G_m,H_n$. As in 103.1,
$D_{m,n}=\sup_{0<t<1}|G_m(t)-H_n(t)|$ almost surely.

For differing laws $F\ne G$ (continuity is not needed here) choose $x$ with
$F(x)\ne G(x)$. Then $D_{m,n}\ge|F_m(x)-G_n(x)|$. The empirical value
$F_m(x)$ is a mean of $m$ independent indicators, with variance at most
$1/(4m)$, so Chebyshev's inequality gives $F_m(x)\to F(x)$ and likewise
$G_n(x)\to G(x)$ in probability. Hence $D_{m,n}\ge|F(x)-G(x)|/2$ with
probability tending to one, while $mn/(m+n)\ge\min(m,n)/2\to\infty$.

**Library results.** `MeasureTheory.Measure.cdf_map_eq_volume_restrict`,
`MeasureTheory.Measure.map_quantile_volume_Ioo` and
`MeasureTheory.Measure.quantile_le_iff` in
`TauCeti/Probability/Quantile.lean`; `MeasureTheory.integral_map` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`;
`ProbabilityTheory.meas_ge_le_variance_div_sq` and
`ProbabilityTheory.IndepFun.variance_sum` in
`Mathlib/Probability/Moments/Variance.lean`.

### 103.31. Optimality of functional principal components

**Statement.** With eigenvalues in decreasing order,
$$\inf_{\dim V=k}\mathbb E\|X-\mu-P_V(X-\mu)\|^2=\sum_{j>k}\lambda_j,$$
the infimum over orthogonal projections onto $k$-dimensional subspaces; the
first $k$ eigenfunctions span a minimizer, unique if
$\lambda_k>\lambda_{k+1}$. The entry is partly covered: TauCeti's Ky Fan
trace inequality gives the deterministic inequality in finite dimension,
through
$\mathbb E\|X-\mu-P_V(X-\mu)\|^2=\mathop{\mathrm{tr}}C-\mathop{\mathrm{tr}}(P_VC)$,
and for a positive operator the bound is attained by some orthonormal
family of $k$ vectors. Missing are the expectation formulation, attainment
by the leading eigenvectors, uniqueness, and the trace-class Hilbert-space
case.

**Scope.** The whole statement when $H$ is finite dimensional, of dimension
$d\ge k$. The infinite-dimensional case, which needs compactness and the
trace-class property of $C$ and a spectral series, remains a substantial gap.

**Argument.** Put $Y=X-\mu$. Let $C$ be Mathlib's covariance operator of the
law of $Y$; since $Y$ is centred, $\langle Cx,y\rangle=\mathbb E\langle x,Y
\rangle\langle y,Y\rangle$, so $C$ is symmetric and positive. Let
$(\varphi_j)$ be an orthonormal eigenbasis with
$\lambda_1\ge\cdots\ge\lambda_d$. For $V$ with orthonormal basis
$w_1,\ldots,w_k$, Pythagoras and Parseval give
$$\mathbb E\|Y-P_VY\|^2=\mathbb E\|Y\|^2-\sum_{i\le k}\mathbb E\langle w_i,Y
\rangle^2=\sum_{j\le d}\lambda_j-\sum_{i\le k}\langle Cw_i,w_i\rangle.$$
Expanding $w_i$ in the eigenbasis, $\sum_i\langle Cw_i,w_i\rangle
=\sum_j\lambda_jc_j$ with $c_j=\|P_V\varphi_j\|^2\in[0,1]$ and
$\sum_jc_j=k$. Using $\sum_{j\le k}(1-c_j)=\sum_{j>k}c_j$,
$$\sum_{j\le k}\lambda_j-\sum_j\lambda_jc_j
\ge\lambda_k\sum_{j\le k}(1-c_j)-\lambda_{k+1}\sum_{j>k}c_j
=(\lambda_k-\lambda_{k+1})\sum_{j>k}c_j\ge0.$$
This is Ky Fan's inequality, which TauCeti states directly for the
orthonormal family $(w_i)$, and gives the lower bound $\sum_{j>k}\lambda_j$.
The span of $\varphi_1,\ldots,\varphi_k$ attains it, since then $c_j=1$ for
$j\le k$ and $c_j=0$ otherwise; TauCeti's attainment theorem for positive
operators gives only some attaining family, so this explicit choice is
used instead.
If $\lambda_k>\lambda_{k+1}$ and $V$ attains it, then $c_j=0$ for $j>k$, so
$V\perp\varphi_j$ for $j>k$ and $V=\mathop{\mathrm{span}}(\varphi_1,\ldots,
\varphi_k)$ by dimension. For $k=d$ put $\lambda_{d+1}=0$; the statement is
then trivial.

**Library results.** `ProbabilityTheory.covarianceOperator`,
`ProbabilityTheory.covarianceOperator_inner` and
`ProbabilityTheory.isPositive_covarianceOperator` in
`Mathlib/Probability/Moments/CovarianceBilin.lean`;
`LinearMap.IsSymmetric.eigenvectorBasis` and
`LinearMap.IsSymmetric.eigenvalues_antitone` in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`;
`LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues` in
`TauCeti/Analysis/InnerProductSpace/KyFan.lean`;
`Submodule.norm_sq_eq_add_norm_sq_starProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`.

### 103.34. Lasso under compatibility

**Statement.** Let $S$ be nonempty and $\lambda>0$. Suppose $\beta$ is
supported on $S$ and $\lambda\ge2n^{-1}\|X^\top\varepsilon\|_\infty$.
If $\kappa(S,3)>0$, every
lasso solution satisfies
$$\frac1n\|X(\hat\beta-\beta)\|_2^2\le\frac{9\lambda^2|S|}{4\kappa^2(S,3)},
\qquad\|\hat\beta-\beta\|_1\le\frac{6\lambda|S|}{\kappa^2(S,3)},$$
and the error lies in the cone $\|\delta_{S^c}\|_1\le3\|\delta_S\|_1$. If
$n^{-1}\|X\delta\|_2^2\ge\kappa\|\delta\|_2^2$ on that cone, then
$\|\hat\beta-\beta\|_2\le3\sqrt{|S|}\lambda/\kappa$. For independent centered
unit-variance sub-Gaussian design entries, there are constants
$C,c,\kappa_0>0$ depending only on the sub-Gaussian parameter such that the
restricted eigenvalue condition holds with $\kappa=\kappa_0$ with
probability at least $1-2e^{-cn}$ when $n\ge C|S|\log(ep/|S|)$; for columns
with $\|X_{\cdot j}\|_2^2/n\le1$ and independent $N(0,\sigma^2)$ errors,
$\lambda=2\sigma\sqrt{2(\log p+t)/n}$ meets the noise condition with
probability at least $1-2e^{-t}$. The deterministic part is
finite-dimensional convex analysis, and the noise event follows from
Mathlib's Gaussian tail bound by a union bound. For random designs,
TauCeti bounds the operator norm of a sub-Gaussian matrix from above with
exponential probability, by a net argument, and bounds covering numbers by
volume; the lower restricted eigenvalue bound, uniform over the cone, is
not stated. The lasso, the cone argument, and the restricted eigenvalue
property of random designs are missing.

**Scope.** The deterministic bounds and the Gaussian noise event. The
restricted eigenvalue property of random sub-Gaussian designs needs a
covering argument with two-sided concentration of $\|Xv\|^2$, uniformly
over the cone, and remains a substantial gap; TauCeti's operator-norm tail
bound for sub-Gaussian matrices controls only the upper side.

**Argument.** The lasso must be introduced as a definition. Put
$\delta=\hat\beta-\beta$ and $a=n^{-1}\|X\delta\|_2^2$. The hypotheses $\lambda>0$
and $S\ne\varnothing$ are retained from the statement: if $\lambda=0$,
the noise condition forces
$X^\top\varepsilon=0$ and $a=0$, but the cone and $\ell^1$ conclusions can
fail. A first-order condition is used, not the basic inequality, which loses
a factor $2$. For $0<t\le1$, the point $\hat\beta-t\delta=(1-t)\hat\beta+t
\beta$ has criterion at least that of $\hat\beta$. The quadratic part is
exactly quadratic in $t$ and the $\ell^1$ norm is convex, so
$$0\le\frac tn\langle Y-X\hat\beta,X\delta\rangle+\frac{t^2}{2n}\|X\delta\|^2
+t\lambda(\|\beta\|_1-\|\hat\beta\|_1).$$
Divide by $t$, let $t\downarrow0$ and use $Y-X\hat\beta=\varepsilon-X\delta$:
$$a\le\frac1n\langle X^\top\varepsilon,\delta\rangle
+\lambda(\|\beta\|_1-\|\hat\beta\|_1)
\le\frac\lambda2\|\delta\|_1+\lambda(\|\delta_S\|_1-\|\delta_{S^c}\|_1)
=\frac{3\lambda}2\|\delta_S\|_1-\frac\lambda2\|\delta_{S^c}\|_1,$$
using Hölder and $\|\beta\|_1-\|\hat\beta\|_1\le\|\delta_S\|_1-\|\delta_{S^c}
\|_1$ for $\beta$ supported on $S$. Since $a\ge0$, $\delta$ lies in the cone.
The definition of $\kappa=\kappa(S,3)$ gives $\|\delta_S\|_1\le\sqrt{|S|a}/
\kappa$, so $a\le\frac{3\lambda}2\sqrt{|S|a}/\kappa$ and
$a\le9\lambda^2|S|/(4\kappa^2)$. In the cone,
$\|\delta\|_1\le4\|\delta_S\|_1\le4\sqrt{|S|a}/\kappa\le6\lambda|S|/\kappa^2$.
Under the restricted eigenvalue condition,
$\kappa\|\delta\|_2^2\le a\le\frac{3\lambda}2\sqrt{|S|}\,\|\delta\|_2$, which
gives $\|\delta\|_2\le3\sqrt{|S|}\lambda/(2\kappa)$, better than stated.

Noise event: $Z_j=n^{-1}X_{\cdot j}^\top\varepsilon$ is a linear combination
of independent centred Gaussians, hence sub-Gaussian with variance proxy
$\sigma^2\|X_{\cdot j}\|^2/n^2\le\sigma^2/n$. The Chernoff bound for $Z_j$
and $-Z_j$ gives
$P(|Z_j|\ge\lambda/2)\le2\exp(-(\log p+t))=2e^{-t}/p$, and a union bound
over the $p$ columns gives $1-2e^{-t}$.

**Library results.** `ProbabilityTheory.HasSubgaussianMGF`,
`ProbabilityTheory.HasSubgaussianMGF.const_mul`,
`ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun` and
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` in
`Mathlib/Probability/Moments/SubGaussian.lean`;
`ProbabilityTheory.mgf_gaussianReal` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`; `measure_iUnion_le`
for the union bound. The deterministic part uses only finite sums and the
Cauchy–Schwarz inequality.

### 103.37. Benjamini–Hochberg procedure

**Statement.** Fix $\alpha\in(0,1)$, let $k=\max\{i:p_{(i)}\le i\alpha/m\}$
($k=0$ if no such $i$), and reject the hypotheses of
$p_{(1)},\ldots,p_{(k)}$. If the null $p$-values are independent of each
other and of the non-null ones, or if the $p$-value vector $p$ is positively
regression dependent on the subset of null coordinates, then
$$\mathbb E\Bigl[\frac V{\max(R,1)}\Bigr]\le\alpha\frac{m_0}m\le\alpha.$$
No library defines $p$-values or multiple-testing procedures; the
argument is finite and combinatorial–probabilistic, but no part is present.

**Scope.** The independence case. Only the independence of each null
$p_i$ from the vector of the other $p$-values is used. The positive
regression dependence case needs a monotonicity argument for conditional
laws and remains a gap.

**Argument.** Validity means $P(p_i\le u)\le u$ for true nulls $i$ and
$u\in[0,1]$. Put $N(u)=\#\{l:p_l\le u\}$; then
$R=\max\{j\le m:N(j\alpha/m)\ge j\}$ (or $0$), and the rejected set is
$\{l:p_l\le R\alpha/m\}$. For a null $i$ let $R^{(i)}$ be the number of
rejections when $p_i$ is replaced by $0$; it is a function of
$(p_l)_{l\ne i}$. Combinatorial lemma: if $p_i\le k\alpha/m$ then
$R=k$ if and only if $R^{(i)}=k$. Indeed, for $j\ge k$ the counts
$N(j\alpha/m)$ and $N^{(i)}(j\alpha/m)$ agree, and $R=k$ means
$N(k\alpha/m)\ge k$ and $N(j\alpha/m)<j$ for $j>k$, and similarly for
$R^{(i)}$. Hence, with $H_0$ the set of true nulls,
$$\mathbb E\frac V{\max(R,1)}=\sum_{i\in H_0}\sum_{k=1}^m\frac1k
P(p_i\le k\alpha/m,\ R^{(i)}=k)
\le\sum_{i\in H_0}\sum_{k=1}^m\frac1k\cdot\frac{k\alpha}m
P(R^{(i)}=k)\le\frac{m_0\alpha}m,$$
by independence of $p_i$ and $R^{(i)}$, validity, and
$\sum_kP(R^{(i)}=k)\le1$. Ties among $p$-values cause no difficulty.
$p$-values and the procedure must be defined; measurability is clear since
$R$ is a finite combination of indicators.

**Library results.** `ProbabilityTheory.IndepFun.measure_inter_preimage_eq_mul`
in `Mathlib/Probability/Independence/Basic.lean`, with
`ProbabilityTheory.iIndepFun.indepFun_finset` to pass from mutual
independence to independence of $p_i$ and $(p_l)_{l\ne i}$; linearity of the
integral for the finite double sum.

### 103.39. Le Cam's two-point method

**Statement.** If two parameters are at distance at least $2s$, every
estimator satisfies
$$\max_{j=0,1}P_j\bigl(d(\hat\theta,\theta_j)\ge s\bigr)
\ge\tfrac12\bigl(1-\|P_0-P_1\|_{\mathrm{TV}}\bigr),$$
so for a nonnegative increasing loss $\ell$ the minimax risk is at least
$\ell(s)(1-\|P_0-P_1\|_{\mathrm{TV}})/2$. For product laws
$P_j=Q_j^{\otimes n}$, $D(P_0\|P_1)=nD(Q_0\|Q_1)$ and
$\|P_0-P_1\|_{\mathrm{TV}}\le\sqrt{D(P_0\|P_1)/2}$. The argument is short: the
test choosing the nearer parameter has errors bounded by the two
probabilities, and the sum of errors of any test is at least
$1-\|P_0-P_1\|_{\mathrm{TV}}$. Statlib proves this testing identity, as the
value of the Bayes risk of testing $P_0$ against $P_1$ under the prior with
unit masses, and the identity $D(Q_0^{\otimes n}\|Q_1^{\otimes n})
=nD(Q_0\|Q_1)$; TauCeti proves Pinsker's inequality, stated for Mathlib's
total variation distance, which is twice the synopsis convention. Missing is
the reduction from an estimator to a test, so the two-point lower bound
itself is not stated.

**Argument.** Test affinity. Statlib's Bayes binary risk for the prior
with unit masses on the two hypotheses is the infimum over measurable
rejection regions $E$ of $P_0(E)+P_1(E^c)$, and also over randomized tests
given by Markov kernels into `Bool`. For probability measures its value is
$1-\frac12\mathrm{tvDist}(P_0,P_1)=1-\|P_0-P_1\|_{\mathrm{TV}}$. Hence
$P_0(E)+P_1(E^c)\ge1-\|P_0-P_1\|_{\mathrm{TV}}$ for every measurable $E$,
and the same holds for randomized tests.

Reduction. Put $E=\{d(\hat\theta,\theta_1)<d(\hat\theta,\theta_0)\}$, which
is measurable for a measurable estimator; for a randomized estimator given
by a Markov kernel, compose it with the indicator of that event to obtain a
randomized test. If $d(\hat\theta,\theta_0)<s$, the triangle inequality and
$d(\theta_0,\theta_1)\ge2s$ give $d(\hat\theta,\theta_1)>s$, so the data
point is not in $E$; thus $P_0(E)\le P_0(d(\hat\theta,\theta_0)\ge s)$, and
symmetrically $P_1(E^c)\le P_1(d(\hat\theta,\theta_1)\ge s)$. The maximum is
at least half the sum. For the risk,
$\mathbb E_j\ell(d(\hat\theta,\theta_j))\ge\ell(s)P_j(d(\hat\theta,\theta_j)
\ge s)$, and the minimax risk is at least the supremum over the two points,
for instance through the two-point prior.

Products. Statlib's tensorization for identical factors gives
$D(Q_0^{\otimes n}\|Q_1^{\otimes n})=nD(Q_0\|Q_1)$ for probability measures.
Pinsker's inequality in TauCeti's form
$\mathrm{etvDist}(P_0,P_1)^2\le2D(P_0\|P_1)$, with
$\mathrm{etvDist}=2\|P_0-P_1\|_{\mathrm{TV}}$ for probability measures, gives
$\|P_0-P_1\|_{\mathrm{TV}}\le\sqrt{D(P_0\|P_1)/2}$; when the divergence is
infinite there is nothing to prove.

**Library results.** `ProbabilityTheory.bayesBinaryRisk`,
`ProbabilityTheory.bayesBinaryRisk_eq_iInf_measurableSet` and
`ProbabilityTheory.bayesBinaryRisk_eq_iInf_kernel` in
`Statlib/Testing/Binary.lean`;
`ProbabilityTheory.bayesBinaryRisk_one_one_eq_ofReal_one_sub_tvDist_div_two`
in `Statlib/Divergence/TotalVariation.lean`;
`ProbabilityTheory.klDiv_pi_const` in
`Statlib/Divergence/KullbackLeibler/CondKL.lean`;
`TauCeti.etvDist_sq_le_two_mul_klDiv` in
`TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean`;
`MeasureTheory.etvDist` and `MeasureTheory.tvDist` in
`Mathlib/MeasureTheory/Measure/TotalVariation/Defs.lean`;
`ProbabilityTheory.minimaxRisk` and `ProbabilityTheory.iSup_bayesRisk_le_minimaxRisk`
in `Mathlib/Probability/Decision/Risk/`.

### 103.40. Fano's method

**Statement.** Let $\theta_1,\ldots,\theta_M$, $M\ge2$, be $2s$-separated
with observation laws $P_j$, let $J$ be uniform on $\{1,\ldots,M\}$ and
$X\mid J=j\sim P_j$. Every estimator satisfies
$$\sup_jP_j\bigl(d(\hat\theta,\theta_j)\ge s\bigr)
\ge1-\frac{I(J;X)+\log2}{\log M},\qquad
I(J;X)=\frac1M\sum_jD(P_j\|\bar P)\le\frac1M\sum_jD(P_j\|Q)$$
for $\bar P=M^{-1}\sum_jP_j$ and any reference law $Q$ with finite right
side. Statlib defines mutual information as the divergence of the joint law
from the product of its marginals and proves the identities from which the
two displayed formulas for $I(J;X)$ follow, and, for a loss with values in
$[0,1]$, the bound $\mathrm{kl}(R_\pi^P,R_\pi^0)\le I(\pi\otimes P)$ of the
binary divergence between the Bayes risk with observations and the Bayes
risk without them. The $M$-ary bound is a short argument from this: under
the $0$–$1$ loss and the uniform prior on $M$ indices every decision without
data has risk $1-1/M$, and a lower bound for the binary divergence turns
the inequality into the display. Missing are this specialization and the
reduction from an estimator to an index test; the $M$-ary Fano bound is not
stated.

**Argument.** Let $\Theta=\{1,\ldots,M\}$ with the discrete structure, $U$
the uniform law on it, and $P$ the Markov kernel $j\mapsto P_j$, so that
the law of $(J,X)$ is $U\otimes P$ and its second marginal is $\bar P$; the
mutual information is Statlib's $I(U\otimes P)$.

Formulas for $I(J;X)$. Statlib expresses $I(U\otimes P)$ as the conditional
divergence of $P$ from the constant kernel at $\bar P$, and since $\Theta$
is countable the conditional divergence is the integral
$\int D(P_j\|\bar P)\,dU(j)=M^{-1}\sum_jD(P_j\|\bar P)$. For a reference
law $Q$, the compensation identity gives
$D(U\otimes P\,\|\,U\times Q)=I(U\otimes P)+D(\bar P\|Q)\ge I(U\otimes P)$,
and the left side is the conditional divergence of $P$ from the constant
kernel at $Q$, which is $M^{-1}\sum_jD(P_j\|Q)$ by the same integral
formula.

Fano bound. Take the action space $\Theta$ and Statlib's $0$–$1$ loss
$\ell(j,z)=1\{j\ne z\}$, which is measurable and bounded by $1$. Without
observations a randomized decision is a probability $\nu$ on $\Theta$, and
its risk under $U$ is $M^{-1}\sum_j(1-\nu\{j\})=1-1/M$, so
$R_U^0=1-1/M$. Statlib's bound gives
$\mathrm{kl}(R_U^P,1-1/M)\le I(U\otimes P)$, and
$\mathrm{kl}(1-p,1-q)=\mathrm{kl}(p,q)$ turns this into
$\mathrm{kl}(a,1/M)\le I(U\otimes P)$ with $a=1-R_U^P$. For $a\in[0,1]$,
$$\mathrm{kl}(a,1/M)=a\log M-h(a)+(1-a)\log\frac M{M-1}\ge a\log M-\log2,$$
with $h$ the binary entropy, so $R_U^P\ge1-(I(J;X)+\log2)/\log M$; this is
trivial when $I(J;X)=\infty$.

Reduction. Let $\psi(x)$ be the index $j$ with
$d(\hat\theta(x),\theta_j)<s$ if there is one, and $1$ otherwise; by
$2s$-separation there is at most one such $j$, and $\psi$ is measurable.
For a randomized estimator compose its kernel with $\psi$. Then
$P_j(d(\hat\theta,\theta_j)\ge s)\ge P_j(\psi\ne j)$, so the supremum is at
least the average error $M^{-1}\sum_jP_j(\psi\ne j)$, which is the risk of
the decision rule $\psi$ and hence at least the Bayes risk $R_U^P$.

**Library results.** `ProbabilityTheory.mutualInfo`,
`ProbabilityTheory.mutualInfo_compProd_eq_condKL` and
`ProbabilityTheory.klDiv_compProd_prod_eq_mutualInfo_add` in
`Statlib/Divergence/MutualInformation/Basic.lean`;
`ProbabilityTheory.condKL` and `ProbabilityTheory.condKL_eq_lintegral` in
`Statlib/Divergence/KullbackLeibler/CondKL.lean`;
`ProbabilityTheory.ofReal_klBerReal_bayesRisk_le_mutualInfo` in
`Statlib/Divergence/MutualInformation/Estimation.lean`;
`ProbabilityTheory.zeroOneLoss` in
`Statlib/ForMathlib/Probability/Decision/ZeroOneLoss.lean`;
`InformationTheory.klBerReal` and `InformationTheory.klBerReal_one_sub` in
`Statlib/ForMathlib/InformationTheory/KullbackLeibler/Bernoulli.lean`;
`MeasureTheory.Measure.compProd_const` in
`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`;
`ProbabilityTheory.bayesRisk` in `Mathlib/Probability/Decision/Risk/Defs.lean`;
`Real.binEntropy_le_log_two` in
`Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`.

### 103.45. Varshamov–Gilbert bound

**Statement.** If $m\ge8$, there are points
$\omega^{(0)}=0,\omega^{(1)},\ldots,\omega^{(M)}$ of $\{0,1\}^m$ with
$\rho(\omega^{(j)},\omega^{(k)})\ge m/8$ for $j<k$ and $M\ge2^{m/8}$.
Mathlib defines the Hamming distance and packing numbers, and TauCeti
develops minimum distances of codes without an existence bound; its
volumetric covering bounds concern balls of normed spaces, not Hamming
balls. The statement follows by a counting argument: the Hamming balls of radius $m/8$
about a maximal separated set cover the cube, and Hoeffding's inequality,
which Mathlib proves, bounds the size of each ball. It is not stated.

**Argument.** The cube is finite, so there is a family $A\ni0$ that is
maximal for the property that distinct points are at Hamming distance at
least $m/8$. By maximality every $\omega$ lies at distance $<m/8$ from some
point of $A$, so
$2^m\le|A|\cdot\#\{\omega:|\omega|<m/8\}$, where $|\omega|=\rho(\omega,0)$.
Under the uniform law on the cube the coordinates are independent
Bernoulli$(1/2)$ variables. The centred variables $\frac12-\omega_i$ take
values in an interval of length $1$, so they are sub-Gaussian with variance
proxy $1/4$. Hoeffding's inequality gives
$$2^{-m}\#\{|\omega|<m/8\}\le P\Bigl(\sum_i(\tfrac12-\omega_i)\ge\tfrac{3m}8
\Bigr)\le\exp\Bigl(-\frac{(3m/8)^2}{2\cdot m/4}\Bigr)=e^{-9m/32}.$$
Hence $|A|\ge e^{9m/32}=2^{cm}$ with $c=9/(32\log2)>0.405$. Then
$M=|A|-1\ge2^{0.405m}-1\ge2^{m/8}$ for $m\ge8$, since
$2^{m/8}(2^{0.28m}-1)\ge2^{m/8}$ once $2^{0.28m}\ge2$.

**Library results.** `hammingDist` in `Mathlib/InformationTheory/Hamming.lean`;
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` and
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` in
`Mathlib/Probability/Moments/SubGaussian.lean`;
`ProbabilityTheory.iIndepFun_pi` in
`Mathlib/Probability/Independence/Basic.lean`.

### 103.46. Assouad's lemma

**Statement.** Let $(P_\omega)_{\omega\in\Omega}$ be laws indexed by
$\Omega=\{0,1\}^m$. For every estimator $\hat\omega$ with values in $\Omega$,
$$\max_\omega E_\omega\rho(\hat\omega,\omega)\ge\frac m2
\min_{\rho(\omega,\omega')=1}\inf_\psi
\bigl(P_\omega(\psi=1)+P_{\omega'}(\psi=0)\bigr).$$
If neighbouring laws satisfy
$\|P_\omega-P_{\omega'}\|_{\mathrm{TV}}\le\alpha<1$, the right side is at
least $m(1-\alpha)/2$; if instead $D(P_\omega\|P_{\omega'})\le\alpha<\infty$,
it is at least $\frac m2\max(\frac12e^{-\alpha},1-\sqrt{\alpha/2})$. If
$d(\theta_\omega,\theta_{\omega'})^2\ge c\rho(\omega,\omega')$, every
estimator $\hat\theta$ obeys
$\max_\omega E_\omega d(\hat\theta,\theta_\omega)^2\ge
(c/4)\max_\omega E_\omega\rho(\hat\omega,\omega)$ for a nearest index
$\hat\omega$. The lemma combines $m$ two-point bounds of the kind in
103.39. For each neighbouring pair, Statlib's testing identity gives the
total-variation form of the bound and its Bretagnolle–Huber inequality the
term $\frac12e^{-\alpha}$, and TauCeti's Pinsker inequality the term
$1-\sqrt{\alpha/2}$; the reduction from the hypercube to its edges is not
stated. Mathlib's Assouad bound on dual VC dimension is unrelated.

**Argument.** The maximum is at least the average over $\Omega$, and
$\rho(\hat\omega,\omega)=\sum_j1\{\hat\omega_j\ne\omega_j\}$. For fixed $j$,
pair each $\omega$ with $\omega_j=0$ with its neighbour $\omega'$ obtained
by flipping coordinate $j$. With the test $\psi=\hat\omega_j$,
$P_\omega(\hat\omega_j\ne\omega_j)+P_{\omega'}(\hat\omega_j\ne\omega'_j)
=P_\omega(\psi=1)+P_{\omega'}(\psi=0)$, which is at least the minimum on the
right. There are $2^{m-1}$ pairs for each of the $m$ coordinates, so the
average is at least $2^{-m}\cdot m\cdot2^{m-1}$ times the minimum.

The infimum over tests equals $1-\|P_\omega-P_{\omega'}\|_{\mathrm{TV}}$ by
Statlib's testing identity, as in 103.39, which gives the total variation
form. In the divergence form, $1-\sqrt{\alpha/2}$ follows from Pinsker's
inequality as in 103.39, and $\frac12e^{-\alpha}$ is Statlib's
Bretagnolle–Huber inequality $e^{-D(P\|Q)}\le2-\mathrm{tvDist}(P,Q)$, that
is, $1-\|P-Q\|_{\mathrm{TV}}\ge\frac12e^{-D(P\|Q)}$, which Statlib states for
probability measures of finite divergence.

For the metric statement, let $\hat\omega$ be a measurable nearest index
(finite set, fixed tie-breaking). Then
$d(\theta_{\hat\omega},\theta_\omega)\le d(\theta_{\hat\omega},\hat\theta)+
d(\hat\theta,\theta_\omega)\le2d(\hat\theta,\theta_\omega)$, so
$c\rho(\hat\omega,\omega)\le4d(\hat\theta,\theta_\omega)^2$ pointwise.

**Library results.** The testing identity and Pinsker step as in 103.39
(`ProbabilityTheory.bayesBinaryRisk_eq_iInf_measurableSet`,
`ProbabilityTheory.bayesBinaryRisk_one_one_eq_ofReal_one_sub_tvDist_div_two`,
`TauCeti.etvDist_sq_le_two_mul_klDiv`);
`ProbabilityTheory.exp_neg_klDiv_le_two_sub_tvDist` in
`Statlib/Divergence/BretagnolleHuber.lean`.

### 103.48. Restricted nullspace and exact recovery

**Statement.** For every $\beta$ supported in $S$, basis pursuit with
$y=X\beta$ has the unique solution $\beta$ if and only if $X$ has the
restricted nullspace property with respect to $S$. If
$\delta_{2s}(n^{-1/2}X)<1/3$, the property holds for every $S$ with
$|S|\le s$. For independent centered unit-variance sub-Gaussian entries there
are $C,c>0$, depending only on the sub-Gaussian parameter, such that
$\delta_{2s}(n^{-1/2}X)<1/3$ with probability at least $1-2e^{-cn}$ whenever
$n\ge Cs\log(ep/s)$. The equivalence and the restricted-isometry criterion
are finite-dimensional linear algebra not present in any of the three
libraries. For the probabilistic part TauCeti supplies an operator-norm
tail bound for sub-Gaussian matrices, proved by a net argument, and
volumetric covering bounds; the two-sided isometry bound uniformly over
sparse supports is absent.

**Scope.** The equivalence and the restricted-isometry criterion. The
probabilistic part remains a substantial gap.

**Argument.** Equivalence. Suppose the property holds and $b\ne\beta$ with
$Xb=X\beta$. Then $v=b-\beta$ is a nonzero kernel vector, so
$\|v_{S^c}\|_1>\|v_S\|_1$, and
$\|b\|_1=\|\beta_S+v_S\|_1+\|v_{S^c}\|_1\ge\|\beta\|_1-\|v_S\|_1+
\|v_{S^c}\|_1>\|\beta\|_1$. Conversely, if $v\ne0$ is in the kernel with
$\|v_{S^c}\|_1\le\|v_S\|_1$, then $\beta=v_S$ is supported in $S$, and
$b=-v_{S^c}\ne\beta$ satisfies $Xb=X\beta$ and $\|b\|_1\le\|\beta\|_1$,
which contradicts uniqueness.

Restricted isometry criterion. Write $A=n^{-1/2}X$ and
$\delta=\delta_{2s}(A)$; then $\delta_s(A)\le\delta$. For unit vectors
$u,w$ with disjoint supports of size at most $s$, polarization gives
$\langle Au,Aw\rangle=\frac14(\|A(u+w)\|^2-\|A(u-w)\|^2)\le\delta$, so
$|\langle Au,Aw\rangle|\le\delta\|u\|\|w\|$ in general. Let $v\ne0$ be in
the kernel. Let $S_0$ index its $s$ largest entries in absolute value,
$S_1$ the next $s$, and so on. Each entry on $S_k$, $k\ge1$, is at most
$\|v_{S_{k-1}}\|_1/s$, so $\|v_{S_k}\|_2\le s^{-1/2}\|v_{S_{k-1}}\|_1$ and
$\sum_{k\ge1}\|v_{S_k}\|_2\le s^{-1/2}\|v\|_1$. Since $Av=0$,
$$(1-\delta)\|v_{S_0}\|_2^2\le\|Av_{S_0}\|^2=-\sum_{k\ge1}\langle Av_{S_0},
Av_{S_k}\rangle\le\delta\|v_{S_0}\|_2\sum_{k\ge1}\|v_{S_k}\|_2.$$
With $r=\delta/(1-\delta)$, which is less than $1/2$ because $\delta<1/3$,
this gives $\|v_{S_0}\|_1\le\sqrt s\|v_{S_0}\|_2\le r\|v\|_1$. For
$|S|\le s$, $\|v_S\|_1\le\|v_{S_0}\|_1\le r(\|v_S\|_1+\|v_{S^c}\|_1)$, hence
$\|v_S\|_1\le\frac r{1-r}\|v_{S^c}\|_1$ with $r/(1-r)<1$. If also
$\|v_{S^c}\|_1\le\|v_S\|_1$, then $v_S=0$ and so $v=0$, a contradiction.
The restricted isometry constant must be defined; the least admissible
$\delta$ exists because the admissible set is closed.

**Library results.** Finite-dimensional linear algebra only: kernels of
matrices, `real_inner_le_norm` and the polarization identity in
`Mathlib/Analysis/InnerProductSpace/Basic.lean`, and sorting a finite family
by absolute value (`Finset.sort` or a sorting permutation).

### 103.52. Thresholded covariance estimation

**Statement.** Let $A$ be the $0$–$1$ pattern of the nonzero entries of
$\Sigma$ and $s$ the largest number of nonzero entries in a row. If
$\|\hat\Sigma-\Sigma\|_{\max}\le\lambda$, then
$\|T_\lambda(\hat\Sigma)-\Sigma\|_{\mathrm{op}}\le2\lambda\|A\|_{\mathrm{op}}
\le2s\lambda$. If each coordinate is $\sigma$-sub-Gaussian and $n>\log p$,
$\lambda=\sigma^2(8\sqrt{(\log p)/n}+\delta)$ makes this event hold with
probability at least $1-8e^{-n\min(\delta,\delta^2)/16}$. TauCeti bounds the
operator norm of a matrix with small entries by a dimension-dependent factor,
has Chebyshev-type entrywise deviation bounds for sample second-moment
matrices, and proves Bernstein's inequality and a Bernstein-type tail for
sums of independent sub-exponential variables. Missing are the
sparsity-adapted operator-norm bound, the sub-exponential property of
products of sub-Gaussian coordinates, and hence the exponential entrywise
concentration of $\hat\Sigma$.

**Scope.** The deterministic bound. The probability bound remains a gap:
TauCeti's sub-exponential tail supplies the scalar inequality, but the
sub-exponential moment-generating bound for products of sub-Gaussian
coordinates, with the constants of the statement, is not available.

**Argument.** Put $E=T_\lambda(\hat\Sigma)-\Sigma$. Entrywise: if
$\Sigma_{jk}=0$, then $|\hat\Sigma_{jk}|\le\lambda$, so the thresholded entry
is $0$ and $E_{jk}=0$. If $\Sigma_{jk}\ne0$ and $|\hat\Sigma_{jk}|>\lambda$,
then $|E_{jk}|=|\hat\Sigma_{jk}-\Sigma_{jk}|\le\lambda$. Otherwise
$|E_{jk}|=|\Sigma_{jk}|\le|\Sigma_{jk}-\hat\Sigma_{jk}|+|\hat\Sigma_{jk}|
\le2\lambda$. Hence $|E_{jk}|\le2\lambda A_{jk}$. For unit vectors $x,y$,
$$|x^\top Ey|\le\sum_{j,k}|E_{jk}||x_j||y_k|\le2\lambda\,|x|^\top A|y|
\le2\lambda\|A\|_{\mathrm{op}},$$
so $\|E\|_{\mathrm{op}}\le2\lambda\|A\|_{\mathrm{op}}$. Since $A$ is
symmetric with row and column sums at most $s$,
$|x|^\top A|y|\le\sum_{j,k}A_{jk}(x_j^2+y_k^2)/2\le s$, so
$\|A\|_{\mathrm{op}}\le s$. No randomness is involved.

**Library results.** `Matrix.l2_opNorm_def` and `Matrix.l2_opNorm_mulVec` in
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`;
`ContinuousLinearMap.opNorm_le_bound` in
`Mathlib/Analysis/Normed/Operator/Basic.lean`; finite sums.

### 103.54. Perturbation of the leading eigenvector

**Statement.** Let $\Sigma$ be symmetric positive semidefinite with
eigenvalues $\gamma_1>\gamma_2\ge\cdots$, gap $\nu=\gamma_1-\gamma_2$, and
unit leading eigenvector $\theta^*$, and let $P$ be symmetric with
$\|P\|_{\mathrm{op}}<\nu/2$. Then $\Sigma+P$ has a leading unit eigenvector
$\hat\theta$, unique up to sign, and with
$\langle\hat\theta,\theta^*\rangle\ge0$,
$$\|\hat\theta-\theta^*\|_2\le
\frac{2\|(I-\theta^*\theta^{*\top})P\theta^*\|_2}{\nu-2\|P\|_{\mathrm{op}}}.$$
In the spiked model, with probability at least
$1-c_1\exp(-c_2n\min(\sqrt\nu\,\delta,\nu\delta^2))$ the leading sample
eigenvector satisfies
$\|\hat\theta-\theta^*\|_2\le c_0\sqrt{(\nu+1)\nu^{-2}p/n}+\delta$, with
universal constants $c_0,c_1,c_2$ (hypotheses as in `GAPS.md`). TauCeti's
Davis–Kahan theorem with Weyl's bound gives the sine of the angle at most
$\|P\|_{\mathrm{op}}/(\nu-\|P\|_{\mathrm{op}})$, and its Yu–Wang–Samworth
eigenvector bound gives, for a suitable sign,
$\|\hat\theta-\theta^*\|_2\le2\sqrt2\|P\|_{\mathrm{op}}/\nu$; these are bounds
of the same type with the full perturbation norm. Its residual $\sin\Theta$
theorem in unitarily invariant norms gives the stated form by a short
argument. Missing are the residual form as stated, uniqueness of the leading
eigenvector, and the spiked-model bound.

**Scope.** The deterministic part: uniqueness and the residual bound. The
spiked-model bound needs concentration of sample covariance matrices and
remains a gap.

**Argument.** Positive semidefiniteness is not used. Assume $p\ge2$; for
$p=1$ there is nothing to prove. Put $\hat\Sigma=\Sigma+P$ and
$\eta=\|P\|_{\mathrm{op}}$. Weyl's bound gives
$\lambda_1(\hat\Sigma)\ge\gamma_1-\eta>\gamma_2+\eta\ge\lambda_2(\hat\Sigma)$,
so the top eigenvalue is simple and $\hat\theta$ is unique up to sign. Let
$U=\mathop{\mathrm{span}}\hat\theta$, which is invariant under $\hat\Sigma$.
On $U^\perp$ the eigenvalues of $\hat\Sigma$ are at most $\gamma_2+\eta$.
Apply the residual Davis–Kahan theorem with $F=\mathbb R$, the map
$X:t\mapsto t\theta^*$, and the scalar $M=m:=\gamma_1+\theta^{*\top}P
\theta^*\ge\gamma_1-\eta$, with interval $[m,m]$ and
$\delta=\nu-2\eta>0$. The eigenvalues on $U^\perp$ lie at most at
$m-\delta$, so outside $(m-\delta,m+\delta)$. The residual is
$$\hat\Sigma X-XM:\ t\mapsto t\bigl(\gamma_1\theta^*+P\theta^*-m\theta^*\bigr)
=t\,(I-\theta^*\theta^{*\top})P\theta^*,$$
and the Frobenius norm of a map $t\mapsto tv$ is $\|v\|$. The theorem gives
$\delta\sin\angle(\hat\theta,\theta^*)=\delta\|P_{U^\perp}\theta^*\|\le
\|(I-\theta^*\theta^{*\top})P\theta^*\|$. With
$c=\langle\hat\theta,\theta^*\rangle\in[0,1]$,
$\|\hat\theta-\theta^*\|^2=2(1-c)\le2(1-c^2)=2\sin^2$, so
$\|\hat\theta-\theta^*\|\le\sqrt2\sin\angle\le2\|(I-\theta^*\theta^{*\top})
P\theta^*\|/(\nu-2\eta)$. TauCeti's Yu–Wang–Samworth eigenvector bound,
applied with the gap $\nu$ of $\Sigma$, gives the different bound
$2\sqrt2\eta/\nu$ directly; it does not give the residual form, so the
Sylvester form of the $\sin\Theta$ theorem is used here.

**Library results.**
`TauCeti.UnitarilyInvariantSeminorm.mul_frobenius_starProjection_comp_le_frobenius_sylvester_apply`
in `TauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/SinTheta/Corollaries.lean`
(general form `mul_map_starProjection_comp_le_map_sylvester_apply` in
`.../SinTheta/Basic.lean`), with the hypothesis
`Module.End.PointIntervalExteriorGap` from
`TauCeti/Analysis/InnerProductSpace/PointSpectrum.lean`;
`LinearMap.IsSymmetric.abs_eigenvalue_sub_eigenvalue_le_norm` in
`TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`;
`LinearMap.IsSymmetric.eigenvectorBasis` in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`.

## 104. Bayesian inference and stochastic computation

### 104.10. Highest posterior density regions

**Statement.** A highest posterior density region of posterior content
exactly $1-\alpha$ with $k_\alpha>0$ has the smallest Lebesgue volume among
measurable sets of posterior content at least $1-\alpha$. For a posterior on
the line symmetric about $c$ and nonincreasing in $|\theta-c|$, it may be
taken to be the equal-tailed interval. The construction is not invariant
under reparameterization: there are posterior densities on the line and
increasing smooth bijections $g$ for which $g(C)$ is not a highest posterior
density region of the image posterior. The volume-minimality needs a bathtub
(Neyman–Pearson type) lemma for densities, which is absent; no part of the
entry is stated.

**Argument.** Write $\pi=\pi(\cdot\mid x)$, $\Pi$ for the posterior and
$|\cdot|$ for Lebesgue measure. The bathtub lemma is a one-line
computation. Let $k>0$ and $\{\pi>k\}\subset C\subset\{\pi\ge k\}$ with
$\Pi(C)=1-\alpha$, and let $A$ be measurable with $\Pi(A)\ge1-\alpha$.
Markov's inequality gives $|C|\le|\{\pi\ge k\}|\le1/k<\infty$, and we may
assume $|A|<\infty$. Then $(1_C-1_A)(\pi-k)\ge0$ pointwise, because
$\pi\ge k$ on $C\setminus A$ and $\pi\le k$ on $A\setminus C$. Integrating,
$$k(|C|-|A|)\le\Pi(C)-\Pi(A)\le0,$$
so $|C|\le|A|$. Only the inclusions, $k>0$ and $\Pi(C)=1-\alpha$ are used,
not the maximality defining $k_\alpha$.

Symmetric case. The posterior has a density, so $r\mapsto\Pi([c-r,c+r])$ is
continuous and increases from $0$ to $1$. The intermediate value theorem
gives $r$ with $\Pi(I)=1-\alpha$ for $I=[c-r,c+r]$, and by symmetry each
tail has content $\alpha/2$. Put $k'=\pi(c+r)=\pi(c-r)$. Monotonicity in
$|\theta-c|$ gives $\{\pi>k'\}\subset I\subset\{\pi\ge k'\}$. If $\alpha>0$
then $k'>0$: otherwise $\pi=0$ off $I$ and $\Pi(I)=1$. The bathtub
computation then shows that $I$ has minimal volume. This is the sense in
which the region may be taken to be the equal-tailed interval. The level
$k'$ agrees with $k_\alpha$ up to the endpoints of $I$, which do not affect
volumes or contents.

Non-invariance. Take $\pi(\theta)=2\theta$ on $(0,1)$ and $0<\alpha<1$.
Then $\Pi(\pi\ge k)=1-k^2/4$, so $k_\alpha=2\sqrt\alpha>0$ and
$C=[\sqrt\alpha,1)$. Under the smooth increasing bijection
$g(\theta)=\theta^3$ of $\mathbb R$, the image density is
$\frac23\varphi^{-1/3}$ on $(0,1)$, which is strictly decreasing and
unbounded near $0$. Every set $\{\text{density}>k\}$ with $k$ finite
contains an interval $(0,\epsilon)$, which is disjoint from
$g(C)=[\alpha^{3/2},1)$. So $g(C)$ is not a highest posterior density
region; the image's region is $(0,(1-\alpha)^{3/2}]$.

**Library results.** `MeasureTheory.mul_meas_ge_le_lintegral₀` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`;
`MeasureTheory.setIntegral_mono_on` in
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`; `intermediate_value_Icc`
for the choice of $r$; the change of variables formula on the line for the
image density.

### 104.14. Tweedie's formula and Robbins' estimator

**Statement.** Let $f(x\mid\theta)=h(x)\exp(\theta\cdot x-\psi(\theta))$ on
$\mathbb R^k$, let the prior $g$ be arbitrary, and let the marginal density
$m$ be positive and differentiable under the integral sign. Then
$\mathbb E[\theta\mid X=x]=\nabla\log m(x)-\nabla\log h(x)$. For Poisson
sampling with any prior on $(0,\infty)$,
$\mathbb E[\theta\mid X=x]=(x+1)m(x+1)/m(x)$ with $m$ the marginal mass
function, and for independent $X_1,\ldots,X_n$ with law $m$ and
$N_n(x)=\#\{i\le n:X_i=x\}$, Robbins' estimator $(x+1)N_n(x+1)/N_n(x)$
converges almost surely to $\mathbb E[\theta\mid X=x]$ whenever $m(x)>0$.
The formulas are a differentiation under the integral in the posterior
density formula of Mathlib, and Robbins' limit follows from the strong law
applied to the two counts; none of this is stated. TauCeti's
one-dimensional Gaussian integration by parts is the corresponding identity
for the normal location model only.

**Argument.** Posterior means. By Bayes' formula the posterior is the prior
with density $f(x\mid\theta)/m(x)$. For the Poisson model the data space
$\mathbb N$ is countable, so $\kappa(\theta)\ll\kappa\circ g$ for
$g$-almost every $\theta$: a point of marginal mass $0$ has
$\kappa(\theta)$-mass $0$ for almost every $\theta$, and there are
countably many points. Mathlib's density form of the posterior then gives,
for every $x$ with $m(x)>0$,
$$\mathbb E[\theta\mid X=x]=\frac1{m(x)}\int\theta\,e^{-\theta}
\frac{\theta^x}{x!}\,g(d\theta)=\frac{x+1}{m(x)}\int e^{-\theta}
\frac{\theta^{x+1}}{(x+1)!}\,g(d\theta)=\frac{(x+1)m(x+1)}{m(x)}.$$
This is finite since $m(x+1)\le1$. In the exponential family, write
$m(x)=h(x)L(x)$ with $L(x)=\int e^{\theta\cdot x-\psi(\theta)}g(d\theta)$.
Differentiation under the integral sign, which is the hypothesis, gives
$\nabla L(x)=\int\theta e^{\theta\cdot x-\psi(\theta)}g(d\theta)$. Here
$h$ must be positive and differentiable at $x$. Then
$\nabla\log m=\nabla\log h+\nabla L/L$, and $\nabla L/L$ is the
Bayes-formula posterior mean. In the dominated continuous case,
identifying that version with Mathlib's posterior kernel needs the
Radon–Nikodym derivatives against the marginal to be computed through
Lebesgue densities. This is measure-theoretic bookkeeping valid for almost
every $x$.

Robbins. The indicators $1\{X_i=x\}$ and $1\{X_i=x+1\}$ are independent and
identically distributed with means $m(x)$ and $m(x+1)$. The strong law gives
$N_n(x)/n\to m(x)>0$ and $N_n(x+1)/n\to m(x+1)$ almost surely. Hence
$N_n(x)>0$ eventually and the ratio converges to $(x+1)m(x+1)/m(x)$.

**Library results.** `ProbabilityTheory.posterior_eq_withDensity` in
`Mathlib/Probability/Kernel/Posterior.lean`; `ProbabilityTheory.poissonMeasure`
in `Mathlib/Probability/Distributions/Poisson/Basic.lean`;
`ProbabilityTheory.strong_law_ae` in `Mathlib/Probability/StrongLaw.lean`;
`hasFDerivAt_integral_of_dominated_of_fderiv_le` in
`Mathlib/Analysis/Calculus/ParametricIntegral.lean` when the differentiation
hypothesis is to be verified rather than assumed.

### 104.17. Doob's consistency theorem

**Statement.** Let $\{P_\theta:\theta\in\Theta\}$ be a dominated model on a
standard Borel sample space, with $\Theta$ Polish,
$\theta\mapsto P_\theta(A)$ measurable for every measurable $A$, and
$\theta\mapsto P_\theta$ injective, and let $\Pi$ be a prior. For
$X_1,X_2,\ldots$ independent with law $P_\theta$, there is a $\Pi$-null set
$N$ such that for every $\theta\notin N$ and every neighbourhood $U$ of
$\theta$, the posterior probability of $U$ tends to $1$,
$P_\theta^\infty$-almost surely. Mathlib's Lévy upward theorem gives
almost-sure convergence of the posterior probability of $U$ to its
conditional expectation given the whole sequence; the remaining step is that
$\theta$ is a measurable function of the sequence, which follows from
injectivity, the strong law along a countable generating class, and
measurability of inverses of injective Borel maps. That step and the theorem
are not stated.

**Argument.** Domination is not used. The posterior after $n$ observations
is any fixed version of the conditional law of $\theta$ given
$(X_1,\ldots,X_n)$, for instance Mathlib's `condDistrib` or `posterior`.
The conclusion holds for every such choice.

Joint law. Let $Q$ be the law of $(\theta,X)$ on $\Theta\times\mathcal X^{\mathbb N}$,
the composition product of $\Pi$ with the kernel
$\theta\mapsto P_\theta^\infty=\mathrm{infinitePi}(P_\theta)$. Measurability
of $\theta\mapsto P_\theta^\infty(B)$ holds for cylinders, where it is a
finite product, and extends by the $\pi$–$\lambda$ theorem. Alternatively,
build $Q$ by the Ionescu–Tulcea construction.

$\theta$ is a function of the data. The sample space is standard Borel,
hence countably generated. Let $(A_k)$ be the countable $\pi$-system of
finite intersections of a countable generating family. Under
$P_\theta^\infty$ the coordinates are independent with law $P_\theta$, so
the strong law gives, for each $\theta$ and almost surely,
$n^{-1}\sum_{i\le n}1_{A_k}(X_i)\to P_\theta(A_k)$ for all $k$. Let
$\Phi(x)\in[0,1]^{\mathbb N}$ be the vector of these limits where they exist
and $0$ otherwise; it is measurable. The map
$\varphi(\theta)=(P_\theta(A_k))_k$ is measurable. It is injective, because a
probability measure is determined by its values on a generating
$\pi$-system and $\theta\mapsto P_\theta$ is injective. By Lusin–Souslin,
$\varphi$ is a measurable embedding, so it has a measurable left inverse
$\chi$ on $[0,1]^{\mathbb N}$. Then $T=\chi\circ\Phi$ is
$\sigma(X_1,X_2,\ldots)$-measurable and $T(X)=\theta$ $Q$-almost surely, by
Fubini.

Martingale step. Fix a measurable $U\subset\Theta$. Then
$\Pi_n(U)=\mathbb E_Q[1_U(\theta)\mid X_1,\ldots,X_n]$ $Q$-almost surely.
Since $1_U(\theta)=1_U(T(X))$ $Q$-almost surely and the latter is measurable
for $\bigvee_n\sigma(X_1,\ldots,X_n)$, Lévy's upward theorem gives
$\Pi_n(U)\to1_U(\theta)$ $Q$-almost surely. By Fubini this holds for
$\Pi$-almost every $\theta$, $P_\theta^\infty$-almost surely.

Neighbourhoods. $\Theta$ is second countable. Apply the last step to a
countable base $(U_j)$ and let $N$ be the union of the countably many
exceptional $\Pi$-null sets. For $\theta\notin N$ and a neighbourhood $U$
choose $U_j$ with $\theta\in U_j\subset U$. Then
$\Pi_n(U)\ge\Pi_n(U_j)\to1$ almost surely, because each $\Pi_n$ is a
measure.

**Library results.** `MeasureTheory.Integrable.tendsto_ae_condExp` in
`Mathlib/Probability/Martingale/Convergence.lean`;
`MeasureTheory.condExp_congr_ae` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`;
`ProbabilityTheory.condDistrib_ae_eq_condExp` in
`Mathlib/Probability/Kernel/CondDistrib.lean`; `ProbabilityTheory.posterior`
in `Mathlib/Probability/Kernel/Posterior.lean`;
`Measurable.measurableEmbedding` in
`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`;
`MeasurableEmbedding.exists_measurable_extend` in
`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean`;
`MeasureTheory.Measure.infinitePi` in `Mathlib/Probability/ProductMeasure.lean`;
`ProbabilityTheory.iIndepFun_infinitePi` in
`Mathlib/Probability/Independence/InfinitePi.lean`;
`ProbabilityTheory.strong_law_ae` in `Mathlib/Probability/StrongLaw.lean`;
`MeasurableSpace.countableGeneratingSet` in
`Mathlib/MeasureTheory/MeasurableSpace/CountablyGenerated.lean`;
`MeasureTheory.ext_of_generate_finite` in
`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`;
`MeasureTheory.Measure.ae_compProd_iff` in
`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`.

### 104.22. Metropolis–Hastings

**Statement.** The kernel that proposes $Y\sim q(x,\cdot)$ and moves to $Y$
with probability $\alpha(x,Y)$, remaining at $x$ otherwise, is reversible
with respect to $\pi$ and therefore leaves $\pi$ invariant. Mathlib proves
that a reversible Markov kernel leaves its measure invariant; reversibility
is the one computation that
$\pi(x)q(x,y)\alpha(x,y)=\min(\pi(x)q(x,y),\pi(y)q(y,x))$ is symmetric in
$(x,y)$, the rejection part being concentrated on the diagonal. The kernel
and this computation are not formalized.

**Argument.** Fix a $\sigma$-finite reference measure $\lambda$. Let $\pi$
be a measurable density, and $q$ a jointly measurable function with
$\int q(x,y)\,\lambda(dy)=1$ for every $x$. Define the kernel by
$$K(x,B)=\int_Bq(x,y)\alpha(x,y)\,\lambda(dy)+r(x)1_B(x),\qquad
r(x)=1-\int q(x,y)\alpha(x,y)\,\lambda(dy),$$
the sum of a kernel with density and $r$ times the identity kernel. Since
$0\le\alpha\le1$, $r\ge0$ and $K$ is Markov. If $\pi(x)q(x,y)>0$, then
$\pi(x)q(x,y)\alpha(x,y)=\min(\pi(x)q(x,y),\pi(y)q(y,x))$ from the
definition of $\alpha$. If $\pi(x)q(x,y)=0$, both sides vanish. So
$s(x,y)=\pi(x)q(x,y)\alpha(x,y)$ is symmetric. For measurable $A,B$,
$$\int_AK(x,B)\pi(x)\,\lambda(dx)=\iint1_A(x)1_B(y)s(x,y)\,\lambda(dy)\,
\lambda(dx)+\int_{A\cap B}r\pi\,d\lambda.$$
By Tonelli and the symmetry of $s$ this is symmetric in $(A,B)$, which is
Mathlib's reversibility. Mathlib's theorem then gives invariance of the
measure $\pi\lambda$. The measure need not be normalized.

**Library results.** `ProbabilityTheory.Kernel.IsReversible` and
`ProbabilityTheory.Kernel.IsReversible.invariant` in
`Mathlib/Probability/Kernel/Invariance.lean`;
`ProbabilityTheory.Kernel.withDensity` in
`Mathlib/Probability/Kernel/WithDensity.lean`; `ProbabilityTheory.Kernel.id`
and kernel sums; `MeasureTheory.lintegral_lintegral_swap` in
`Mathlib/MeasureTheory/Measure/Prod.lean`.

### 104.32. Independence and random-walk samplers

**Statement.** For the independence sampler with $q(x,y)=g(y)$ and
$\pi\le Mg$ on the support of $\pi$,
$\sup_A|P^n(x,A)-\pi(A)|\le(1-1/M)^n$ for every $x$; if $\pi/g$ is not
essentially bounded, the chain is not geometrically ergodic. A random-walk
sampler on $\mathbb R$ with symmetric positive increment density is
geometrically ergodic only if $\int e^{s|x|}\pi(dx)<\infty$ for some $s>0$,
and it is geometrically ergodic if $\pi$ is symmetric and
$\log\pi(x)-\log\pi(y)\ge a|y-x|$ for some $a>0$ and $x_1$ whenever
$x_1\le x<y$ or $y<x\le-x_1$. No part is present.

**Scope.** The two statements on the independence sampler, with $\pi,g$
probability densities against Lebesgue measure and $\pi\le Mg$ pointwise on
$\{\pi>0\}$. The random-walk statements need drift criteria and remain a
substantial gap.

**Argument.** Minorization. Put $\epsilon=1/M$; then $M\ge1$. On
$\{\pi>0\}$ we have $g>0$ and $g(x)/\pi(x)\ge\epsilon$. If $\pi(x)>0$, then
$$g(y)\alpha(x,y)=\min\Bigl(g(y),\frac{\pi(y)g(x)}{\pi(x)}\Bigr)\ge
\min(g(y),\epsilon\pi(y))\ge\epsilon\pi(y),$$
using $\pi(y)\le Mg(y)$ where $\pi(y)>0$. If $\pi(x)=0$, then $\alpha=1$ and
$g\ge\epsilon\pi$ again. Hence $P(x,\cdot)\ge\epsilon\pi$ for every $x$. If
$\epsilon=1$ then $P(x,\cdot)=\pi$ and the bound is trivial. Otherwise
$P=\epsilon\Pi+(1-\epsilon)R$ with $\Pi(x,\cdot)=\pi$ and a Markov kernel
$R$.

Contraction. Write $\|\mu-\nu\|=\sup_A|\mu(A)-\nu(A)|$. For probability
measures, $\mu P-\nu P=(1-\epsilon)(\mu R-\nu R)$. If $S$ is a Hahn set
where $\mu\ge\nu$, then $0\le R(\cdot,A)\le1$ gives
$(\mu R-\nu R)(A)=\int R(\cdot,A)\,d(\mu-\nu)\le(\mu-\nu)(S)=\|\mu-\nu\|$,
and symmetrically, so $\|\mu R-\nu R\|\le\|\mu-\nu\|$. Since $\pi P=\pi$ by
104.22, induction gives
$\|\delta_xP^n-\pi\|=\|\delta_xP^n-\pi P^n\|\le(1-\epsilon)^n$.

Failure of geometric ergodicity. The definition must be introduced: there
are $\rho<1$ and $C(x)<\infty$ for $\pi$-almost every $x$ with
$\|P^n(x,\cdot)-\pi\|\le C(x)\rho^n$. For $\pi(x)>0$, the bound
$\alpha(x,y)\le\pi(y)g(x)/(\pi(x)g(y))$ gives
$P(x,\{x\}^c)\le g(x)/\pi(x)=:\eta(x)$. Hence $P^n(x,\{x\})\ge(1-\eta(x))^n$
while $\pi(\{x\})=0$, so $\|P^n(x,\cdot)-\pi\|\ge(1-\eta(x))^n$. If $\pi/g$
is not $\pi$-essentially bounded, the set $\{\eta<1-\rho\}$ has positive
$\pi$-measure. It therefore contains a non-exceptional $x$, for which
$(1-\eta(x))^n\le C(x)\rho^n$ fails for large $n$.

**Library results.** `MeasureTheory.exists_isHahnDecomposition` in
`Mathlib/MeasureTheory/Measure/Decomposition/Hahn.lean`;
`ProbabilityTheory.Kernel.IsReversible.invariant` in
`Mathlib/Probability/Kernel/Invariance.lean`, through 104.22; kernel
composition (`ProbabilityTheory.Kernel.comp`,
`MeasureTheory.Measure.bind`).

### 104.35. Hamiltonian Monte Carlo

**Statement.** The map $\Phi$ preserves Lebesgue measure on
$\mathbb R^{2d}$ and is reversible: $\Phi(x,p)=(x',p')$ implies
$\Phi(x',-p')=(x,-p)$. Drawing $p\sim N(0,M)$, computing
$(x',p')=\Phi(x,p)$, and moving to $x'$ with probability
$\min(1,\exp(H(x,p)-H(x',p')))$ gives a kernel that leaves $\pi$ invariant.
Neither the leapfrog map, its volume preservation as a composition of
shears, nor the Metropolis–Hastings argument with an involutive proposal is
present.

**Argument.** Volume. The leapfrog step is the composition of the shears
$(x,p)\mapsto(x,p-\frac\varepsilon2\nabla U(x))$,
$(x,p)\mapsto(x+\varepsilon M^{-1}p,p)$ and the first shear again. Each
shear preserves Lebesgue measure on $\mathbb R^d\times\mathbb R^d$ by the
skew-product theorem, since every fibre map is a translation. The middle
shear is conjugated by the coordinate swap. They are measurable because
$\nabla U$ is continuous. Compositions preserve measure, so $\Phi$ does.

Reversibility. Let $S(x,p)=(x,-p)$. If one step $\ell$ maps $(x,p)$ to
$(x',p')$, then from $(x',-p')$ the half-step momentum is $-p_{1/2}$, the
position returns to $x$, and the final momentum is $-p$. Thus
$S\ell S\ell=\mathrm{id}$, and by induction $S\Phi S\Phi=\mathrm{id}$, so
$\tau=S\Phi$ is a measure-preserving involution.

Invariance. Let $\rho=e^{-H}$, which is integrable when $e^{-U}$ is.
Normalized, it is the density of $\pi\otimes N(0,M)$, where $N(0,M)$ is
taken as the law with density proportional to
$e^{-p^\top M^{-1}p/2}$. Since $H\circ S=H$, the acceptance probability is
$a(z)=\min(1,\rho(\tau z)/\rho(z))$. For measurable $f\ge0$, substituting
$z=\tau w$,
$$\int f(\tau z)a(z)\rho(z)\,dz=\int f(w)\min(\rho(\tau w),\rho(w))\,dw
=\int f(w)a(w)\rho(w)\,dw.$$
Hence the kernel $z\mapsto a(z)\delta_{\tau z}+(1-a(z))\delta_z$ preserves
$\rho\,dz$. Refreshing $p\sim N(0,M)$ preserves $\pi\otimes N(0,M)$, and the
composite preserves it too. The kernel of the statement moves $x$ to the
first coordinate of $\tau z$ or of $z$, which is $x'$ or $x$: the sign of
$p$ is irrelevant. So if $x\sim\pi$ the new position has law $\pi$.

**Library results.** `MeasureTheory.MeasurePreserving.skew_product` and
`MeasureTheory.Measure.measurePreserving_swap` in
`Mathlib/MeasureTheory/Measure/Prod.lean`; `MeasureTheory.measurePreserving_add_left`
and `MeasureTheory.measurePreserving_neg` (additive forms in
`Mathlib/MeasureTheory/Group/Measure.lean`);
`MeasureTheory.MeasurePreserving.lintegral_comp` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`;
`ProbabilityTheory.Kernel.Invariant.comp` in
`Mathlib/Probability/Kernel/Invariance.lean`.

### 104.68. Score error and total variation

**Statement.** Under the first hypotheses of 104.63, let $P$ be the path law
of the exact reversal, let $s_t(x)$ be measurable in $(t,x)$ and globally
Lipschitz in $x$ uniformly in $t$, and let $Q$ be the law of the reverse
equation with $s$ in place of the score and initial law $\eta$. If
$\mathop{\mathrm{KL}}(p_T\|\eta)<\infty$ and
$\sup_{t,x}\|g(t)^\top(s_t(x)-\nabla\log p_t(x))\|<\infty$, then
$$\mathop{\mathrm{KL}}(P\|Q)\le\mathop{\mathrm{KL}}(p_T\|\eta)
+\frac12\int_0^T\mathbb E_{p_t}\|g(t)^\top(s_t-\nabla\log p_t)\|^2\,dt,$$
and the total variation distance between $p_0$ and the endpoint law of $Q$
is at most $\sqrt{\mathop{\mathrm{KL}}(P\|Q)/2}$. Mathlib's data-processing
inequality and TauCeti's Pinsker inequality give the last step. TauCeti
proves Girsanov's theorem for a constant drift only, and stochastic
integrals are absent; the Girsanov bound is missing.

**Scope.** Only the final total variation bound, given probability measures
$P,Q$ on path space with $P$ having endpoint law $p_0$. The Girsanov bound,
and the stochastic calculus it needs, remain a substantial gap; TauCeti's
constant-drift Girsanov theorem does not cover the state-dependent drift
$s_t-\nabla\log p_t$.

**Argument.** Let $e(\omega)=\omega(T)$, which is measurable on path space.
Then $e_\ast P=p_0$, and $e_\ast Q$ is the endpoint law of $Q$. Data
processing gives $D(p_0\|e_\ast Q)\le D(P\|Q)$. Pinsker's inequality for
events gives $2(p_0(A)-e_\ast Q(A))^2\le D(P\|Q)$ for every measurable $A$.
Take the supremum over $A$.

**Library results.** `InformationTheory.klDiv_map_le` in
`Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean`;
`TauCeti.two_mul_sq_measureReal_sub_le_klDiv` in
`TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean`.

### 104.77. Half-bridges and iterative proportional fitting

**Statement.** If $\mathop{\mathrm{KL}}(\mu_0\|P_0)<\infty$, the unique
half-bridge with initial law $\mu_0$ is $\frac{d\mu_0}{dP_0}(X_0)\cdot P$,
with value $\mathop{\mathrm{KL}}(\mu_0\|P_0)$; if
$\mathop{\mathrm{KL}}(\mu_T\|P_T)<\infty$, the unique half-bridge with
terminal law $\mu_T$ is $\frac{d\mu_T}{dP_T}(X_T)\cdot P$. Every iterate has
the form $f_k(X_0)g_k(X_T)\cdot R$ and its endpoint couplings are the
Sinkhorn iterates for $R_{0T}$. If $P^*$ is the Schrödinger bridge with
$\mathop{\mathrm{KL}}(P^*\|R)<\infty$, then
$\mathop{\mathrm{KL}}(P^*\|P^k)=\mathop{\mathrm{KL}}(P^*\|P^{k+1})
+\mathop{\mathrm{KL}}(P^{k+1}\|P^k)$, so $\mathop{\mathrm{KL}}(P^*\|P^k)$ is
nonincreasing, $\sum_k\mathop{\mathrm{KL}}(P^{k+1}\|P^k)\le
\mathop{\mathrm{KL}}(P^*\|R)$, and the endpoint marginals converge to
$\mu_0,\mu_T$ in relative entropy and in total variation. If
$R_{0T}\ll\mu_0\otimes\mu_T$ with density $e^{-c}$, $c$ bounded below and
$\int e^{rc}\,d(\mu_0\otimes\mu_T)<\infty$ for some $r>1$, then
$\mathop{\mathrm{KL}}(P^*\|P^k)\to0$ and the endpoint couplings converge in
total variation to that of $P^*$. TauCeti proves the half-bridge as a general
entropy projection, and for the static iteration the telescoping identity,
monotonicity, and convergence of the marginal errors. Missing are the
iteration on path space and the convergence of the couplings under the
integrability condition.

**Scope.** Everything except the final sentence of the statement: the
convergence $\mathop{\mathrm{KL}}(P^*\|P^k)\to0$ and of the couplings under
the integrability condition remains a substantial gap. The argument uses
only that $P^*$ has endpoint laws $\mu_0,\mu_T$ and
$\mathop{\mathrm{KL}}(P^*\|R)<\infty$, not its optimality.

**Argument.** TauCeti's projection theorems hold for any finite measure
$\pi$ on any measurable space and any measurable $f$. Take $\pi=P$ on path
space and $f=X_0$ or $f=X_T$. The reweighting `fitLaw` is
$\frac{d\mu_0}{dP_0}(X_0)\cdot P$. When $\mathop{\mathrm{KL}}(\mu_0\|P_0)
<\infty$, so that $\mu_0\ll P_0$, it has initial law $\mu_0$ and
divergence $\mathop{\mathrm{KL}}(\mu_0\|P_0)$ from $P$. It minimizes among
measures with that law, and is the unique minimizer by the uniqueness
theorem. The terminal case is the same.

Form of the iterates. Induct with $P^{k+1}=P^k\,.\mathrm{fitLaw}\,X_0\,\mu_0$
or with $X_T$; a density $h(X_0)$ multiplies the density $f_k(X_0)g_k(X_T)$
against $R$. Endpoint couplings: for $E=(X_0,X_T)$ and a density of the form
$h(X_0)$, $E_\ast(h(X_0)\cdot\pi)=h(x_0)\cdot E_\ast\pi$, which is the change
of variables formula. Also $(E_\ast\pi)_0=\pi_0$. So
$E_\ast P^{k+1}=(E_\ast P^k)\,.\mathrm{fitLaw}\,\mathrm{fst}\,\mu_0$, which
is a Sinkhorn step for $R_{0T}$.

Telescoping. Apply the Pythagorean identity with $\sigma=P^*$, $\pi=P^k$ and
the fitted coordinate:
$\mathop{\mathrm{KL}}(P^*\|P^k)=\mathop{\mathrm{KL}}(\mu\|(P^k)_\bullet)+
\mathop{\mathrm{KL}}(P^*\|P^{k+1})$. The first term is
$\mathop{\mathrm{KL}}(P^{k+1}\|P^k)$, once $\mu\ll(P^k)_\bullet$ is known.
That holds by induction, since the identity bounds
$\mathop{\mathrm{KL}}(\mu\|(P^k)_\bullet)$ by
$\mathop{\mathrm{KL}}(P^*\|P^k)\le\mathop{\mathrm{KL}}(P^*\|R)<\infty$.
Monotonicity and the summability bound follow by summation. The marginal
not fitted at step $k+1$ has error
$\mathop{\mathrm{KL}}(\mu\|(P^{k+1})_\bullet)=\mathop{\mathrm{KL}}(P^{k+2}\|
P^{k+1})$, which tends to $0$. Pinsker's inequality for events turns this
into total variation convergence.

**Library results.** `MeasureTheory.Measure.fitLaw`,
`MeasureTheory.Measure.rnDeriv_fitLaw`,
`MeasureTheory.Measure.map_fitLaw_of_absolutelyContinuous`,
`MeasureTheory.Measure.isFiniteMeasure_fitLaw`,
`TauCeti.klDiv_eq_klDiv_map_add_klDiv_fitLaw`, `TauCeti.klDiv_fitLaw`,
`TauCeti.klDiv_fitLaw_le` and `TauCeti.eq_fitLaw_of_klDiv_le` in
`TauCeti/InformationTheory/KullbackLeibler/Projection.lean`; the static
iteration `MeasureTheory.Measure.proportionalFitting` in
`TauCeti/MeasureTheory/OptimalTransport/ProportionalFitting.lean`, to which
the endpoint couplings reduce up to the order of the two half-steps;
`TauCeti.two_mul_sq_measureReal_sub_le_klDiv` in
`TauCeti/InformationTheory/KullbackLeibler/Pinsker.lean`;
`MeasureTheory.withDensity_mul` in
`Mathlib/MeasureTheory/Measure/WithDensity.lean`;
`MeasureTheory.lintegral_map` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`.

## 105. Linear models, multivariate analysis, experimental design, and causal inference

### 105.1. Gauss–Markov theorem

**Statement.** Assume $\mathbb E\varepsilon=0$ and
$\mathop{\mathrm{Cov}}(\varepsilon)=\sigma^2I_n$. Among linear unbiased
estimators of an estimable functional $c^\top\beta$, the least-squares
estimator has the smallest variance. If $X$ has full column rank,
$\sigma^2(X^\top X)^{-1}$ is the Loewner minimum of the covariances of linear
unbiased estimators of $\beta$. None of the three libraries defines the
linear model or its estimators; the theorem follows from Mathlib's orthogonal projection by a
short argument.

**Argument.** Let $V=\mathop{\mathrm{col}}X$ and $P$ the orthogonal
projection onto $V$. A linear estimator $a^\top Y$ is unbiased for
$c^\top\beta$ if and only if $a^\top X\beta=c^\top\beta$ for all $\beta$,
that is $X^\top a=c$; estimability of $c^\top\beta$ means that such an $a$
exists. The least-squares fitted vector is $X\hat\beta=PY$, and for any
unbiased $a$ the least-squares estimator of $c^\top\beta$ is
$$
c^\top\hat\beta=a^\top X\hat\beta=a^\top PY=(Pa)^\top Y,
$$
by symmetry of $P$; in particular it does not depend on the choice of $a$
or of the solution $\hat\beta$ of the normal equations, and it is itself
unbiased because $X^\top Pa=(PX)^\top a=X^\top a=c$. With
$\mathop{\mathrm{Cov}}(\varepsilon)=\sigma^2I_n$ the double-sum formula for
the variance of a linear combination gives
$\mathop{\mathrm{Var}}(a^\top Y)=\sigma^2\|a\|^2$, and Pythagoras gives
$$
\sigma^2\|a\|^2=\sigma^2\|Pa\|^2+\sigma^2\|(I-P)a\|^2
\ge\sigma^2\|Pa\|^2=\mathop{\mathrm{Var}}(c^\top\hat\beta),
$$
with equality only if $a=Pa$, i.e. only for the least-squares estimator
itself.

For the Loewner form, let $BY$ be linear and unbiased for $\beta$, so that
$BX=I_p$. For $u\in\mathbb R^p$, $u^\top BY$ is linear and unbiased for
$u^\top\beta$, so $u^\top\mathop{\mathrm{Cov}}(BY)u
=\mathop{\mathrm{Var}}(u^\top BY)\ge\mathop{\mathrm{Var}}(u^\top\hat\beta)$.
Under full column rank $X^\top X$ is invertible,
$\hat\beta=(X^\top X)^{-1}X^\top Y$, and
$\mathop{\mathrm{Var}}(u^\top\hat\beta)=\sigma^2u^\top(X^\top X)^{-1}u$. Since
this holds for every $u$,
$\mathop{\mathrm{Cov}}(BY)-\sigma^2(X^\top X)^{-1}$ is positive
semidefinite, and the bound is attained by $\hat\beta$. Only uncorrelated
homoscedastic errors are used; no normality is needed.

**Library results.** `Submodule.starProjection`,
`Submodule.inner_starProjection_left_eq_right`,
`Submodule.starProjection_eq_self_iff` and
`Submodule.norm_sq_eq_add_norm_sq_starProjection`, and
`Submodule.starProjection_minimal` (the nearest-point property, which
identifies $PY$ with the least-squares fit), in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
`ProbabilityTheory.variance_sum` in `Mathlib/Probability/Moments/Variance.lean`;
`Matrix.rank_transpose_mul_self` in `Mathlib/LinearAlgebra/Matrix/Rank.lean`.
The linear model and its unbiased linear estimators are new definitions.

### 105.2. Normal sampling theory

**Statement.** If $\varepsilon\sim N(0,\sigma^2I_n)$, then
$\|PY\|^2/\sigma^2$ is noncentral chi-squared on $r$ degrees of freedom with
noncentrality $\|P\mu\|^2/\sigma^2$, where $\mu=\mathbb EY$, and it is
independent of $\|(I-P)Y\|^2$; the residual sum of squares
$\|(I-P)Y\|^2/\sigma^2$ is chi-squared on $n-r$ degrees of freedom. When $X$
has full column rank, the least-squares estimator is normal with mean $\beta$
and covariance $\sigma^2(X^\top X)^{-1}$ and is independent of the residual
sum of squares. TauCeti proves the case $\mu=0$, $\sigma=1$: for a standard
Gaussian vector, the squared lengths of its projections onto pairwise
orthogonal subspaces are independent chi-squared variables on the respective
dimensions. TauCeti also defines the noncentral chi-squared law, proves that
a sum of squares of independent $N(m_i,1)$ variables, and the squared norm of
an $N_n(m,I_n)$ vector, have that law with noncentrality $\sum_im_i^2$,
respectively $\|m\|^2$, and proves that affine images of Gaussian vectors are
Gaussian. Not stated are the noncentral law of $\|PY\|^2/\sigma^2$ for
general $\mu$ and $\sigma$, its independence of the residual sum of squares,
and the law of the least-squares estimator; they follow by a short argument.

**Argument.** Write $Y=\mu+\sigma Z$ with $Z$ standard Gaussian on
$\mathbb R^n$ and $\mu=X\beta\in V=\mathop{\mathrm{col}}X$, so that
$PY=\mu+\sigma PZ$ and $(I-P)Y=\sigma(I-P)Z$. By TauCeti's projection
theorems for the pair of orthogonal subspaces $V$ and $V^\perp$, the
projections $PZ$ and $(I-P)Z$ are independent, $PZ$ is standard Gaussian
on $V$, and $\|(I-P)Z\|^2$ has the chi-squared law on $n-r$ degrees of
freedom. Hence $\|(I-P)Y\|^2/\sigma^2=\|(I-P)Z\|^2\sim\chi^2_{n-r}$, and
every function of $PY$ is independent of the residual sum of squares.

For the noncentral law, choose an orthonormal basis $b_1,\ldots,b_r$ of $V$.
The standard Gaussian on $V$ is the image of the product of $r$ standard
real Gaussians under $\xi\mapsto\sum_i\xi_ib_i$, so
$PZ=\sum_i\xi_ib_i$ with $\xi_1,\ldots,\xi_r$ independent $N(0,1)$, and
$$
\frac{\|PY\|^2}{\sigma^2}=\sum_{i\le r}(\xi_i+m_i)^2,\qquad
m_i=\frac{\langle\mu,b_i\rangle}\sigma .
$$
The variables $\xi_i+m_i$ are independent $N(m_i,1)$, and TauCeti's
noncentral sum-of-squares theorem gives the noncentral chi-squared law on
$r$ degrees of freedom with noncentrality
$\sum_im_i^2=\|P\mu\|^2/\sigma^2=\|\mu\|^2/\sigma^2$.

Under full column rank,
$\hat\beta=(X^\top X)^{-1}X^\top Y=(X^\top X)^{-1}X^\top PY$ is a function
of $PY$, hence independent of the residual sum of squares, and it is the
affine image $\beta+\sigma(X^\top X)^{-1}X^\top Z$ of a standard Gaussian,
hence Gaussian with covariance
$\sigma^2(X^\top X)^{-1}X^\top X(X^\top X)^{-1}=\sigma^2(X^\top X)^{-1}$.
The degenerate cases $r=0$ and $r=n$ give the Dirac law at $0$ for the
corresponding sum, which is the zero-dimensional case of the TauCeti laws.

**Library results.**
`Submodule.map_orthogonalProjectionOnto_stdGaussian`,
`Submodule.map_norm_sq_starProjection_stdGaussian` and
`TauCeti.Probability.iIndepFun_orthogonalProjectionOnto_stdGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Projection.lean`;
`TauCeti.Probability.noncentralChiSquaredMeasure` in
`TauCeti/Probability/Distributions/NoncentralChiSquared/Basic.lean`;
`TauCeti.Probability.map_sum_sq_pi_gaussianReal_noncentral` in
`TauCeti/Probability/Distributions/NoncentralChiSquared/Gaussian.lean`;
`TauCeti.Probability.map_affine_multivariateGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Affine.lean`;
`ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`;
`ProbabilityTheory.gaussianReal_map_add_const` in
`Mathlib/Probability/Distributions/Gaussian/Real.lean`;
`ProbabilityTheory.iIndepFun.comp` in
`Mathlib/Probability/Independence/Basic.lean`.

### 105.10. Exact tests of nested linear models

**Statement.** Let $P_0,P_1$ project onto nested model spaces of dimensions
$r_0<r_1<n$. Under the smaller model and independent $N(0,\sigma^2)$ errors,
$$\frac{\|(P_1-P_0)Y\|^2/(r_1-r_0)}
{\|(I-P_1)Y\|^2/(n-r_1)}\sim F_{r_1-r_0,n-r_1},$$
the numerator and denominator sums of squares, divided by $\sigma^2$, being
independent chi-squared variables. Under the larger model the numerator has
noncentrality $\|(P_1-P_0)X\beta\|^2/\sigma^2$, and a single estimable
contrast gives the square of the Student $t$ statistic. TauCeti proves the
Fisher and Student constructions from independent chi-squared variables, and
the noncentral $F$ law of the ratio when the numerator is noncentral. None of
the three libraries states the test; the null statement follows from
TauCeti's projection laws and Fisher construction by a short argument, and
the noncentral numerator law under the larger model follows as in 105.2.

**Argument.** Let $V_0\subset V_1$ be the model spaces and write
$Y=\mu+\sigma Z$ with $Z$ standard Gaussian and $\mu=X\beta\in V_1$. The
subspaces $W=V_1\cap V_0^\perp$, of dimension $r_1-r_0$, and $V_1^\perp$, of
dimension $n-r_1$, are orthogonal, $P_1-P_0$ is the projection onto $W$, and
$$
(P_1-P_0)Y=(P_1-P_0)\mu+\sigma(P_1-P_0)Z,\qquad
(I-P_1)Y=\sigma(I-P_1)Z .
$$
By TauCeti's projection theorems, $(P_1-P_0)Z$ and $(I-P_1)Z$ are
independent and $\|(I-P_1)Z\|^2\sim\chi^2_{n-r_1}$. Under the smaller model
$\mu\in V_0$, so $(P_1-P_0)\mu=0$ and $\|(P_1-P_0)Z\|^2\sim\chi^2_{r_1-r_0}$;
the two sums of squares divided by $\sigma^2$ are independent chi-squared
variables, and TauCeti's Fisher construction gives the $F_{r_1-r_0,n-r_1}$
law of the ratio (the factors $\sigma^2$ cancel). Under the larger model the
computation of 105.2 with $W$ in place of the column space gives the
noncentral chi-squared law on $r_1-r_0$ degrees of freedom with noncentrality
$\|(P_1-P_0)\mu\|^2/\sigma^2$ for the numerator, still independent of the
denominator, and TauCeti's noncentral $F$ construction then gives the law of
the ratio.

For a single contrast, let the smaller model be $V_0=\{X\beta:c^\top\beta=0\}$
inside $V_1=\mathop{\mathrm{col}}X$, with $c^\top\beta$ estimable and not
identically zero, so that $r_1-r_0=1$. If $a^\top Y$ is unbiased for
$c^\top\beta$, then $w=P_1a$ is orthogonal to $V_0$ (for $X\beta\in V_0$,
$\langle w,X\beta\rangle=c^\top\beta=0$), nonzero, and lies in $V_1$, so
$(P_1-P_0)Y=\langle w,Y\rangle w/\|w\|^2$. By 105.1,
$\langle w,Y\rangle=c^\top\hat\beta$ and
$\mathop{\mathrm{Var}}(c^\top\hat\beta)=\sigma^2\|w\|^2$. Hence, with
$s^2=\|(I-P_1)Y\|^2/(n-r_1)$, the $F$ statistic equals $t^2$ for
$t=c^\top\hat\beta/(s\|w\|)$, the usual $t$ statistic; under the null,
$c^\top\hat\beta/(\sigma\|w\|)$ is standard normal and independent of
$s^2/\sigma^2$, so TauCeti's Student construction gives $t\sim t_{n-r_1}$.

**Library results.** As for 105.2, together with
`TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared` in
`TauCeti/Probability/Distributions/FisherSnedecor/ChiSquared.lean`,
`TauCeti.Probability.hasLaw_studentT_of_gaussian_chiSquared` in
`TauCeti/Probability/Distributions/StudentT/ChiSquared.lean`, and
`TauCeti.Probability.hasLaw_noncentralF_of_noncentralChiSquared` in
`TauCeti/Probability/Distributions/NoncentralF/Basic.lean`.

### 105.15. Distribution of quadratic forms

**Statement.** Let $Y\sim N_n(\mu,\Sigma)$ with $\Sigma$ positive definite,
and let $A,B$ be symmetric. If $A\Sigma$ is idempotent of rank $r$, then
$Y^\top AY$ is noncentral chi-squared on $r$ degrees of freedom with
noncentrality $\mu^\top A\mu$; for $\mu=0$, $Y^\top AY$ is chi-squared on $r$
degrees of freedom only if $A\Sigma$ is idempotent of rank $r$. If
$A\Sigma B=0$, then $Y^\top AY$ and $Y^\top BY$ are independent, and for
$\mu=0$ this condition is also necessary (Craig–Sakamoto). For $\Sigma=I_n$
(Cochran's theorem): if $Y^\top Y=\sum_{i=1}^kY^\top A_iY$ with
$\mathop{\mathrm{rank}}A_i=n_i$, the forms $Y^\top A_iY$ are independent
noncentral chi-squared variables on $n_i$ degrees of freedom with
noncentralities $\mu^\top A_i\mu$ if and only if $\sum_in_i=n$. TauCeti
computes the moment-generating function of a centred Gaussian quadratic form
and the chi-squared moment-generating function, proves the chi-squared laws
and independence of squared Gaussian projections, the noncentral
chi-squared law of $\|Y\|^2$ for identity covariance, and the criterion that
linear images $AY$ and $BY$ of a Gaussian vector are independent if and
only if $A\Sigma B^\top=0$. No law of a quadratic form $Y^\top AY$ is
stated; the sufficiency of idempotence, its converse for $\mu=0$, the
sufficiency half of Craig–Sakamoto, and Cochran's theorem follow by short
arguments. The necessity half of Craig–Sakamoto is missing.

**Scope.** The argument covers everything except the necessity half of
Craig–Sakamoto (that independence of $Y^\top AY$ and $Y^\top BY$ for $\mu=0$
forces $A\Sigma B=0$), which remains a substantial gap.

**Argument.** Noncentral chi-squared is TauCeti's law, written
$\chi^2_k(\delta)$. Write $S=\Sigma^{1/2}$ (positive definite, symmetric) and
$Y=\mu+SZ$ with $Z$ standard Gaussian.

*Sufficiency of idempotence.* Put $C=SAS$, symmetric. If $A\Sigma$ is
idempotent then $A\Sigma A\Sigma=A\Sigma$, so $A\Sigma A=A$ and
$C^2=SA\Sigma AS=C$; thus $C$ is the orthogonal projection onto its range,
of rank $\mathop{\mathrm{rank}}A=\mathop{\mathrm{rank}}A\Sigma=r$. With
$m=S^{-1}\mu$,
$$
Y^\top AY=(Z+m)^\top C(Z+m)=\|C(Z+m)\|^2,
$$
and the computation of 105.2 with $P=C$ (a basis adapted to the range of
$C$) shows that this is $\chi^2_r(\|Cm\|^2)$, with
$\|Cm\|^2=m^\top Cm=\mu^\top A\mu$.

*Necessity for $\mu=0$.* Suppose $Q=Y^\top AY$ has law $\chi^2_r$. TauCeti
shows that $e^{tQ}$ is integrable if and only if $I-2tC$ is positive
definite, i.e. $2t\lambda_j<1$ for every eigenvalue $\lambda_j$ of $C$. The
chi-squared law has a finite exponential moment for every $t<1/2$ (a Gamma
integral), so $2t\lambda_j<1$ for all $t<1/2$, which forces
$0\le\lambda_j\le1$. On $t<1/2$ the two moment-generating functions agree:
$$
\prod_j(1-2t\lambda_j)^{-1/2}=\det(I-2tC)^{-1/2}=(1-2t)^{-r/2}.
$$
Squaring and inverting, the polynomials $\prod_j(1-2t\lambda_j)$ and
$(1-2t)^r$ agree on an infinite set, hence are equal; by unique
factorization the nonzero $\lambda_j$ are exactly $r$ ones. So $C$ is a
symmetric matrix with eigenvalues in $\{0,1\}$, hence idempotent of rank $r$,
and $A\Sigma=S^{-1}CS$ is idempotent of rank $r$.

The same comparison gives the central case directly: if $A\Sigma$ is
idempotent of rank $r$, then both moment-generating functions equal
$(1-2t)^{-r/2}$ on $t<1/2$. Equality on an open interval containing $0$ is
turned into equality of laws by analytic continuation: both complex
moment-generating functions are analytic on the strip
$\{\mathop{\mathrm{Re}}z<1/2\}$, agree on the real segment, hence agree on
the strip, which contains the imaginary axis; equal characteristic functions
give equal laws. (Mathlib states the uniqueness theorem only under equality
of the complex moment-generating functions; the strip argument above is the
needed specialization.)

*Sufficiency in Craig–Sakamoto.* By the spectral theorem
$A=\sum_{\lambda_i\ne0}\lambda_iv_iv_i^\top$, so
$Y^\top AY=\sum\lambda_i(v_i^\top Y)^2$ and
$v_i^\top Y=\lambda_i^{-1}v_i^\top(AY)$; thus $Y^\top AY$ is a measurable
function of $AY$, and likewise $Y^\top BY$ of $BY$. Since $B$ is symmetric,
$A\Sigma B^\top=A\Sigma B=0$, and TauCeti's independence criterion for
linear images of a Gaussian vector gives the independence of $AY$ and $BY$,
hence of the quadratic forms.

*Cochran's theorem.* Here $\Sigma=I$, the $A_i$ are symmetric, and
$\sum_iA_i=I$ (the identity of quadratic forms for all $Y$). If
$\sum_in_i=n$, then $\mathbb R^n=\sum_i\mathop{\mathrm{ran}}A_i$ (since
$x=\sum_iA_ix$) and the dimensions add up to $n$, so the sum is direct. For
$x\in\mathop{\mathrm{ran}}A_j$, the decompositions $x=\sum_iA_ix$ and $x=x$
coincide, so $A_ix=0$ for $i\ne j$ and $A_jx=x$; hence
$A_iA_j=\delta_{ij}A_j$. Each $A_i$ is a symmetric idempotent of rank
$n_i$, so $Y^\top A_iY\sim\chi^2_{n_i}(\mu^\top A_i\mu)$ by the first part.
The ranges of the $A_i$ are mutually orthogonal, so the vectors
$A_iY=A_i\mu+A_i(Y-\mu)$ are, up to the constants $A_i\mu$, projections of
a standard Gaussian vector onto orthogonal subspaces, hence mutually
independent by TauCeti's projection theorem, and the forms are functions of
them. Conversely, if the forms are independent with laws
$\chi^2_{n_i}(\mu^\top A_i\mu)$, compare means: a $\chi^2_k(\delta)$ variable
has mean $k+\delta$ (TauCeti's moment formula), so
$\mathbb EY^\top Y=n+\|\mu\|^2$ equals
$\sum_i(n_i+\mu^\top A_i\mu)=\sum_in_i+\|\mu\|^2$, and $\sum_in_i=n$. The
hypothesis of independence is not needed for this direction.

**Library results.**
`TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff`,
`TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
`TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian` in
`TauCeti/Probability/Distributions/Gaussian/QuadraticForm.lean`;
`TauCeti.Probability.mgf_id_chiSquaredMeasure` in
`TauCeti/Probability/Distributions/ChiSquared/Basic.lean`;
`ProbabilityTheory.analyticOnNhd_complexMGF`,
`ProbabilityTheory.complexMGF_ofReal` and
`ProbabilityTheory.complexMGF_mul_I` in
`Mathlib/Probability/Moments/ComplexMGF.lean`;
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` in
`Mathlib/Analysis/Analytic/IsolatedZeros.lean`;
`MeasureTheory.Measure.ext_of_charFun` in
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`;
`Polynomial.eq_of_infinite_eval_eq` in `Mathlib/Algebra/Polynomial/Roots.lean`;
`Matrix.IsHermitian.spectral_theorem` and
`Matrix.IsHermitian.det_eq_prod_eigenvalues` in
`Mathlib/Analysis/Matrix/Spectrum.lean`;
`TauCeti.Probability.indepFun_matrix_multivariateGaussian_iff` in
`TauCeti/Probability/Distributions/Gaussian/Independence.lean`;
`TauCeti.Probability.integral_id_noncentralChiSquaredMeasure` in
`TauCeti/Probability/Distributions/NoncentralChiSquared/Moments.lean`;
the results listed for 105.2.

### 105.22. Wishart distribution and Hotelling's $T^2$

**Statement.** If $Z_1,\ldots,Z_n$ are independent $N_p(0,\Sigma)$ with
$n\ge p$ and $\Sigma$ positive definite, then $\sum_iZ_iZ_i^\top$ has the
Wishart law $W_p(n,\Sigma)$ with its classical density. For an independent
normal sample of size $n\ge p+1$, the sample mean $\bar X$ and the sample
covariance $S$ with divisor $n-1$ are independent,
$(n-1)S\sim W_p(n-1,\Sigma)$, and Hotelling's statistic
$T^2=n(\bar X-\mu)^\top S^{-1}(\bar X-\mu)$ satisfies
$$\frac{n-p}{(n-1)p}\,T^2\sim F_{p,\,n-p}$$
when the true mean is $\mu$. TauCeti proves the first sentence. Not stated
are the independence of $\bar X$ and $S$, the law of $(n-1)S$, and the law
of $T^2$. They follow by a short argument: an orthogonal rotation of the
sample separates $\bar X$ from $n-1$ independent $N_p(0,\Sigma)$ vectors
whose Gram sum is $(n-1)S$, and the law of $T^2$ follows from TauCeti's
Schur-complement law for a block of size one, after a congruence, together
with its Fisher construction.

**Argument.** *Independence and the Wishart law.* Write $X_i=\mu+RG_i$ with $R=\Sigma^{1/2}$ and $G_1,\ldots,G_n$
independent standard Gaussian vectors in $\mathbb R^p$. Stacked, $G$ is a
standard Gaussian on $\mathbb R^{n\times p}$ with its Frobenius inner
product (the product of $np$ standard real Gaussians). Let $H$ be an
orthogonal $n\times n$ matrix whose first row is $n^{-1/2}(1,\ldots,1)$
(extend this unit vector to an orthonormal basis). The map $G\mapsto HG$ is a
linear isometry of $\mathbb R^{n\times p}$, so $G'=HG$ is again standard
Gaussian, i.e. its rows $G'_1,\ldots,G'_n$ are independent standard
Gaussian vectors. Put $Z_k=RG'_k$, independent $N_p(0,\Sigma)$. Then
$Z_1=\sqrt n(\bar X-\mu)$ and, by orthogonality of $H$,
$$
\sum_{i}(X_i-\mu)(X_i-\mu)^\top=\sum_kZ_kZ_k^\top,\qquad
(n-1)S=\sum_i(X_i-\mu)(X_i-\mu)^\top-n(\bar X-\mu)(\bar X-\mu)^\top
=\sum_{k\ge2}Z_kZ_k^\top.
$$
So $\bar X$ is a function of $Z_1$ and $S$ of $(Z_2,\ldots,Z_n)$, which are
independent, and TauCeti's Gram theorem gives
$(n-1)S\sim$ `wishartGramMeasure` $(n-1)$ $\Sigma$, which agrees with the
density law when $n-1\ge p$; this holds for every $n\ge p+1$. The
identification of the row structure of the standard Gaussian on
$\mathbb R^{n\times p}$ is product-measure bookkeeping (equality of
characteristic functions).

*Hotelling's $T^2$.* Put $W=(n-1)S$, Wishart of degree $m=n-1\ge p$ and
scale $\Sigma$, independent of $\bar X$, and $a=\bar X-\mu$, which is
nonzero almost surely. For a fixed $a\ne0$, choose an invertible $M$ with
$M^{-1}e_1=a$ (extend $a$ to a basis). TauCeti's congruence theorem makes
$W'=MWM^\top$ Wishart of degree $m$ and scale $\Sigma'=M\Sigma M^\top$, and
$$
(W'^{-1})_{11}=a^\top W^{-1}a,\qquad(\Sigma'^{-1})_{11}=a^\top\Sigma^{-1}a .
$$
TauCeti's Schur-complement law for a block of size one, applied to $W'$ at
the index $1$ (with scale $\Sigma'=(\Sigma'^{-1})^{-1}$ and real degree
$m>p-1$), shows that
$g(a,W)=a^\top\Sigma^{-1}a/a^\top W^{-1}a$ has the chi-squared law on
$m-p+1=n-p$ degrees of freedom, whatever $a\ne0$. Since $\bar X$ and $W$ are
independent, the joint law of $(a,W)$ is a product, and Fubini's theorem
shows that $V=g(\bar X-\mu,W)$ is $\chi^2_{n-p}$ and independent of
$\bar X$. Moreover $\sqrt n(\bar X-\mu)\sim N_p(0,\Sigma)$, so
$U=n\,a^\top\Sigma^{-1}a$ is the squared norm of a standard Gaussian vector
in $\mathbb R^p$ and has law $\chi^2_p$; it is a function of $\bar X$, hence
independent of $V$. Then
$$
T^2=n(n-1)\,a^\top W^{-1}a=(n-1)\frac UV,\qquad
\frac{n-p}{(n-1)p}\,T^2=\frac{U/p}{V/(n-p)},
$$
and TauCeti's Fisher construction gives the law $F_{p,n-p}$.

**Library results.** `ProbabilityTheory.stdGaussian_map` and
`ProbabilityTheory.map_pi_eq_stdGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`;
`MeasureTheory.Measure.ext_of_charFun` in
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`;
`ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map` and
`ProbabilityTheory.iIndepFun.indepFun_finset` in
`Mathlib/Probability/Independence/Basic.lean`;
`TauCeti.Probability.hasLaw_wishartGram_gaussian` in
`TauCeti/Probability/Distributions/Wishart/Basic.lean`;
`TauCeti.Probability.wishartGramMeasure_eq_nonsingularWishartMeasure` in
`TauCeti/Probability/Distributions/Wishart/Agreement.lean`;
`TauCeti.Probability.map_affine_multivariateGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Affine.lean`;
`TauCeti.Probability.map_symmetricCongruenceLinearMap_nonsingularWishartMeasure`
in `TauCeti/Probability/Distributions/Wishart/Marginal.lean`;
`TauCeti.Probability.map_inv_inv_apply_nonsingularWishartMeasure` in
`TauCeti/Probability/Distributions/Wishart/Inverse/Marginal.lean`;
`TauCeti.Probability.stdGaussian_map_norm_sq` in
`TauCeti/Probability/Distributions/Chi/Gaussian.lean`;
`TauCeti.Probability.hasLaw_fisherSnedecor_of_chiSquared` in
`TauCeti/Probability/Distributions/FisherSnedecor/ChiSquared.lean`;
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map` in
`Mathlib/Probability/Independence/Basic.lean`; `MeasureTheory.lintegral_prod`
in `Mathlib/MeasureTheory/Measure/Prod.lean`.

### 105.28. Gaussian covariance likelihood

**Statement.** For a normal sample with unknown mean and positive definite
covariance, if the centred sample spans $\mathbb R^p$, the maximum likelihood
estimators are $\hat\mu=\bar X$ and
$\hat\Sigma=n^{-1}\sum_i(X_i-\bar X)(X_i-\bar X)^\top$. If that scatter
matrix is singular, the likelihood is unbounded over positive definite
covariances and has no maximizer there; this occurs almost surely when
$n\le p$. TauCeti proves the classical density of a nondegenerate
multivariate Gaussian, which is the likelihood; its maximization is not
stated.

**Argument.** Let $A=\sum_i(X_i-\bar X)(X_i-\bar X)^\top$. From the TauCeti
density, the log-likelihood is
$$
\ell(\mu,\Sigma)=-\tfrac{np}2\log2\pi-\tfrac n2\log\det\Sigma
-\tfrac12\mathop{\mathrm{tr}}(\Sigma^{-1}A)
-\tfrac n2(\bar X-\mu)^\top\Sigma^{-1}(\bar X-\mu),
$$
by the usual splitting $X_i-\mu=(X_i-\bar X)+(\bar X-\mu)$, whose cross terms
sum to zero. For every $\Sigma$ the last term is maximal, with value $0$,
exactly at $\mu=\bar X$, since $\Sigma^{-1}$ is positive definite.

If $A$ is positive definite (the centred sample spans $\mathbb R^p$), write
$A=LL^\top$ with $L$ invertible (from the spectral theorem, $L=UD^{1/2}$)
and put $B=L^\top\Sigma^{-1}L$, positive definite with eigenvalues
$\beta_1,\ldots,\beta_p>0$. Then $\det B=\det A/\det\Sigma$ and
$\mathop{\mathrm{tr}}B=\mathop{\mathrm{tr}}(\Sigma^{-1}A)$, so
$$
\ell(\bar X,\Sigma)=\text{const}+\tfrac12\sum_j(n\log\beta_j-\beta_j).
$$
The function $x\mapsto n\log x-x$ on $(0,\infty)$ has its unique maximum at
$x=n$ (from $\log y\le y-1$ with $y=x/n$, equality only at $y=1$). Hence
$\ell$ is maximal exactly when all $\beta_j=n$, i.e. $B=nI$, i.e.
$\Sigma=A/n$. The maximizer exists and is unique.

If $A$ is singular, take a unit vector $v$ with $Av=0$ and
$\Sigma_\varepsilon=I-vv^\top+\varepsilon vv^\top$, $\varepsilon>0$. Then
$\det\Sigma_\varepsilon=\varepsilon$,
$\Sigma_\varepsilon^{-1}=I-vv^\top+\varepsilon^{-1}vv^\top$ and
$\mathop{\mathrm{tr}}(\Sigma_\varepsilon^{-1}A)=\mathop{\mathrm{tr}}A$, so
$\ell(\bar X,\Sigma_\varepsilon)=\text{const}-\tfrac n2\log\varepsilon\to\infty$
as $\varepsilon\downarrow0$; the likelihood is unbounded and has no
maximizer. When $n\le p$, the centred vectors $X_i-\bar X$ sum to zero and
span a space of dimension at most $n-1<p$, so $A$ is singular for every
sample, not merely almost surely.

**Library results.** `TauCeti.Probability.multivariateGaussian_eq_withDensity`
in `TauCeti/Probability/Distributions/Gaussian/Density.lean`;
`Matrix.IsHermitian.spectral_theorem`,
`Matrix.IsHermitian.det_eq_prod_eigenvalues` and
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` in
`Mathlib/Analysis/Matrix/Spectrum.lean`; `Real.log_le_sub_one_of_pos` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`.

### 105.37. Kiefer–Wolfowitz equivalence

**Statement.** Assume $M(\xi^*)$ is nonsingular. Then $\xi^*$ maximizes
$\det M(\xi)$ if and only if $\max_xf(x)^\top M(\xi^*)^{-1}f(x)=p$, with
equality on the support of $\xi^*$. For a criterion that is concave and
strictly increasing in the Loewner order and differentiable at $M(\xi^*)$,
the design $\xi^*$ is optimal if and only if the directional derivative of
the criterion at $M(\xi^*)$ is nonpositive in the direction of every
one-point design. TauCeti proves concavity of $(\det A)^{1/n}$ on positive
semidefinite matrices; the information matrix of a design and the
equivalence theorem are absent.

**Argument.** The information matrix $M(\xi)=\int ff^\top\,d\xi$ is a new
definition; $f$ is continuous on a compact space, so the integrals exist.
Write $M^*=M(\xi^*)$ and $d(x)=f(x)^\top M^{*-1}f(x)$, a continuous
function. Linearity of the trace under the integral gives
$$
\int d\,d\xi=\mathop{\mathrm{tr}}\bigl(M^{*-1}M(\xi)\bigr),\qquad
\int d\,d\xi^*=\mathop{\mathrm{tr}}I_p=p.
$$

*D-optimality.* Suppose $d\le p$ everywhere. For any design $\xi$, the
matrix $B=M^{*-1/2}M(\xi)M^{*-1/2}$ is positive semidefinite with
eigenvalues $b_j\ge0$, and by the arithmetic–geometric mean inequality
$$
\frac{\det M(\xi)}{\det M^*}=\prod_jb_j\le\Bigl(\frac1p\sum_jb_j\Bigr)^p
=\Bigl(\frac1p\int d\,d\xi\Bigr)^p\le1 .
$$
Conversely, let $\xi^*$ be D-optimal and $x$ a point. For
$\xi_t=(1-t)\xi^*+t\delta_x$, the matrix determinant lemma gives
$$
\det M(\xi_t)=(1-t)^{p-1}\bigl(1-t+t\,d(x)\bigr)\det M^* ,
$$
and the factor $g(t)=(1-t)^{p-1}(1+t(d(x)-1))$ has $g(0)=1$ and
$g'(0)=d(x)-p$; optimality forces $g\le1$ on $[0,1]$, hence $d(x)\le p$.
Since $\int d\,d\xi^*=p$ and $d\le p$, $d=p$ holds $\xi^*$-almost
everywhere; the open set $\{d<p\}$ is $\xi^*$-null and therefore misses the
support, and the maximum of $d$ is $p$.

*General criterion.* Let $\Phi$ be concave on the positive semidefinite
matrices and differentiable at $M^*$ with derivative $D$. If $\xi^*$ is
optimal, then $t\mapsto\Phi(M(\xi_t))$ has a maximum at $t=0$ on $[0,1]$,
so its right derivative $D[M(\delta_x)-M^*]$ is nonpositive. Conversely,
concavity gives, for every design $\xi$ and $t\in(0,1]$,
$$
\Phi(M(\xi))-\Phi(M^*)\le
\frac{\Phi\bigl(M^*+t(M(\xi)-M^*)\bigr)-\Phi(M^*)}{t}
\longrightarrow D[M(\xi)-M^*],
$$
and $M(\xi)-M^*=\int(M(\delta_x)-M^*)\,\xi(dx)$, so by linearity and
continuity of $D$,
$D[M(\xi)-M^*]=\int D[M(\delta_x)-M^*]\,\xi(dx)\le0$. The hypothesis that
$\Phi$ is strictly increasing in the Loewner order is not used.

**Library results.** `Matrix.det_one_add_replicateCol_mul_replicateRow` and
`Matrix.det_add_replicateCol_mul_replicateRow` in
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`;
`Real.geom_mean_le_arith_mean_weighted` in
`Mathlib/Analysis/MeanInequalities.lean`;
`Matrix.IsHermitian.det_eq_prod_eigenvalues` and
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` in
`Mathlib/Analysis/Matrix/Spectrum.lean`;
`ContinuousLinearMap.integral_comp_comm` in
`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`;
`MeasureTheory.Measure.support` in `Mathlib/MeasureTheory/Measure/Support.lean`.
TauCeti's `Matrix.concaveOn_det_rpow`
(`TauCeti/Analysis/Matrix/MinkowskiDeterminant.lean`) is not needed for the
D-criterion by this route, but gives concavity for the criterion
$(\det M)^{1/p}$ in the general part.

### 105.38. Randomization test

**Statement.** Under the sharp null hypothesis that each unit's response is
unchanged by its treatment assignment, redraw the assignment from the
randomization distribution while holding the responses fixed. The induced
law of a test statistic is free of unknown parameters, and the test that
rejects when the observed statistic lies in the upper fraction $\alpha$ of
this law has conditional level at most $\alpha$ given the responses, hence
unconditional level at most $\alpha$; the conditional level equals $\alpha$
when the randomization law is atomless or ties are broken by auxiliary
randomization. Mathlib has the uniform probability on a finite set, but no
randomization test is formulated.

**Argument.** Let the assignment $W$ have the known law $\pi$ on a finite set
of assignments (for complete randomization, the uniform law on subsets of a
given size) and be independent of the potential outcomes. Under the sharp
null the observed response vector $y$ does not depend on $W$, so the joint
law of $(W,y)$ is $\pi\otimes\mathcal L(y)$. For fixed $y$, let
$\nu_y=\pi\circ t(\cdot,y)^{-1}$ be the randomization law of the statistic;
it is determined by $\pi$ and $y$ alone. Put $G_y(c)=\nu_y([c,\infty))$ and
reject when $G_y(t(W,y))\le\alpha$.

The key fact is that for a real random variable $T$ with law $\nu$ and
$G(c)=\nu([c,\infty))$, $\mathbb P(G(T)\le\alpha)\le\alpha$. Indeed $G$ is
nonincreasing, so $\{c:G(c)\le\alpha\}$ is an up-set, either $[c^*,\infty)$
with $G(c^*)\le\alpha$, or $(c^*,\infty)$, whose $\nu$-measure is
$\lim_kG(c^*+1/k)\le\alpha$. Applied to $\nu_y$, this bounds the conditional
rejection probability given $y$ by $\alpha$, and Fubini on the product law
gives the unconditional bound. If $\nu_y$ is atomless, $G_y$ is continuous
and $G_y(T)$ is uniform on $[0,1]$, so the level is exactly $\alpha$. With
auxiliary randomization, choose $c$ and $\gamma\in[0,1]$ with
$\nu_y((c,\infty))\le\alpha\le\nu_y([c,\infty))$ and
$\nu_y((c,\infty))+\gamma\nu_y(\{c\})=\alpha$, and reject with probability
$1$ above $c$ and $\gamma$ at $c$; the conditional level is $\alpha$. (For
a finite assignment set $\nu_y$ is never atomless, so in practice only the
randomized version is exact.)

**Library results.** `ProbabilityTheory.uniformOn` in
`Mathlib/Probability/UniformOn.lean`; `Finset.card_powersetCard` in
`Mathlib/Data/Finset/Powerset.lean`; Fubini for product measures,
`MeasureTheory.lintegral_prod` in `Mathlib/MeasureTheory/Measure/Prod.lean`;
`MeasureTheory.tendsto_measure_iUnion_atTop` in
`Mathlib/MeasureTheory/Measure/Continuity.lean`. The randomization test is
a new definition.

### 105.42. Fisher's inequality and optimality of balanced incomplete blocks

**Statement.** A balanced incomplete block design with $v$ treatments and
$b$ blocks satisfies $b\ge v$. Every block design with $b$ blocks of size
$k<v$ has $\mathop{\mathrm{tr}}C_d\le b(k-1)$, with equality exactly when no
treatment occurs twice in a block. A balanced incomplete block design
attains this bound and has all $v-1$ positive eigenvalues equal to
$\lambda v/k=b(k-1)/(v-1)$; hence, if one exists, it is A-, D-, and
E-optimal among block designs with the same $v$, $b$, $k$, and more
generally it minimizes every criterion of $C_d$ that is convex, invariant
under relabeling of treatments, and nonincreasing under multiplication of
$C_d$ by scalars at least $1$ (Kiefer's universal optimality). Mathlib's
theorem on nondegenerate configurations gives Fisher's inequality in the
case $\lambda=1$. The case $\lambda\ge2$ and all optimality statements are
missing.

**Argument.** Block designs, their incidence matrices $N=(n_{ij})$ and
information matrices $C_d=R-k^{-1}NN^\top$ (all blocks of size $k$, so
$K=kI$) are new definitions. A balanced incomplete block design is binary,
each treatment occurs in $r$ blocks and each pair in $\lambda\ge1$ blocks,
so $NN^\top=(r-\lambda)I+\lambda J$, and counting gives $bk=vr$ and
$\lambda(v-1)=r(k-1)$; with $k<v$ this yields $r>\lambda$.

*Fisher.* For $x\ne0$,
$x^\top NN^\top x=(r-\lambda)\|x\|^2+\lambda(\sum_ix_i)^2>0$, so $NN^\top$
is positive definite, invertible, of rank $v$, and
$v=\mathop{\mathrm{rank}}NN^\top\le\mathop{\mathrm{rank}}N\le b$.

*Trace bound.* $\mathop{\mathrm{tr}}C_d=\sum_ir_i-k^{-1}\sum_{i,j}n_{ij}^2
=bk-k^{-1}\sum_{i,j}n_{ij}^2$. For nonnegative integers $n_{ij}^2\ge n_{ij}$,
with equality iff $n_{ij}\in\{0,1\}$, and $\sum_{i,j}n_{ij}=bk$; hence
$\mathop{\mathrm{tr}}C_d\le bk-b=b(k-1)$, with equality iff the design is
binary. The hypothesis $k<v$ is not needed here.

*Spectrum of a BIBD.* Using $r(k-1)=\lambda(v-1)$,
$$
C_d=rI-\frac{(r-\lambda)I+\lambda J}k=\frac{\lambda v}k\Bigl(I-\frac Jv\Bigr),
$$
whose eigenvalues are $0$ (on the constants) and $\lambda v/k$ with
multiplicity $v-1$; and $\lambda v/k=b(k-1)/(v-1)$ from the two counting
identities.

*A, D, E.* For any connected competitor, $C_d\mathbf 1=0$ and the positive
eigenvalues $\mu_1,\ldots,\mu_{v-1}$ have sum
$\mathop{\mathrm{tr}}C_d\le T:=b(k-1)$. Cauchy–Schwarz gives
$\sum\mu_i^{-1}\ge(v-1)^2/\sum\mu_i\ge(v-1)^2/T$, the
arithmetic–geometric mean inequality gives
$\prod\mu_i\le(T/(v-1))^{v-1}$, and trivially
$\min\mu_i\le T/(v-1)$; the BIBD attains all three bounds.

*Universal optimality.* Let $\Phi$ be defined on symmetric positive
semidefinite matrices with zero row sums, convex, invariant under
simultaneous permutation of rows and columns, and with $\Phi(cC)\le\Phi(C)$
for $c\ge1$. For a competitor $C_d$, the average
$\bar C=(v!)^{-1}\sum_\sigma P_\sigma C_dP_\sigma^\top$ commutes with all
permutation matrices, so $\bar C=xI+yJ$, and zero row sums give
$\bar C=x(I-J/v)$ with $x=\mathop{\mathrm{tr}}C_d/(v-1)$. Jensen's
inequality for the finite average gives $\Phi(\bar C)\le\Phi(C_d)$. If
$\mathop{\mathrm{tr}}C_d>0$, the BIBD matrix is $C^*=c\bar C$ with
$c=T/\mathop{\mathrm{tr}}C_d\ge1$, so $\Phi(C^*)\le\Phi(\bar C)\le\Phi(C_d)$.
If $\mathop{\mathrm{tr}}C_d=0$ then $C_d=0$, and convexity together with
the scaling property gives $\Phi(C)\le\frac12(\Phi(0)+\Phi(2C))
\le\frac12(\Phi(0)+\Phi(C))$, i.e. $\Phi(C^*)\le\Phi(0)$.

**Library results.** `Matrix.rank_mul_le_left`, `Matrix.rank_le_card_width`
and `Matrix.rank_of_isUnit` in `Mathlib/LinearAlgebra/Matrix/Rank.lean`;
`Matrix.PosDef.det_pos` in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`;
`Matrix.IsHermitian.trace_eq_sum_eigenvalues` in
`Mathlib/Analysis/Matrix/Spectrum.lean`;
`Finset.sum_mul_sq_le_sq_mul_sq` in
`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`;
`Real.geom_mean_le_arith_mean_weighted` in
`Mathlib/Analysis/MeanInequalities.lean`; `ConvexOn.map_sum_le` in
`Mathlib/Analysis/Convex/Jensen.lean`.

### 105.44. Latin squares and mutually orthogonal sets

**Statement.** In the additive model with row, column, and treatment effects
for a Latin square of order $n\ge3$, with independent homoscedastic errors,
the spaces of row, column, and treatment contrasts are mutually orthogonal;
the corrected total sum of squares splits into rows, columns, treatments,
and residual with $n-1$, $n-1$, $n-1$, and $(n-1)(n-2)$ degrees of freedom;
and the least-squares estimator of a difference of two treatment effects is
the difference of the treatment means, with variance $2\sigma^2/n$. A set of
$k$ mutually orthogonal Latin squares of order $s$ is equivalent to an
orthogonal array with $s^2$ rows and $k+2$ columns on $s$ symbols of
strength $2$; consequently $k\le s-1$, and the bound is attained when $s$ is
a prime power. Mathlib has Galois fields of every prime-power order; Latin
squares, orthogonal arrays, the bound, and the construction are absent.

**Argument.** Latin squares and orthogonal arrays are new definitions.

*Analysis of variance.* Work in $\mathbb R^{n\times n}$ with indicator
vectors $\rho_i$ (row $i$), $\kappa_j$ (column $j$), $t_\ell$ (cells with
treatment $\ell$); each has $n$ ones, and the Latin property gives
$\langle\rho_i,\kappa_j\rangle=\langle\rho_i,t_\ell\rangle
=\langle\kappa_j,t_\ell\rangle=1$. The contrast spaces
$R=\{\sum a_i\rho_i:\sum a_i=0\}$, and $C$, $T$ likewise, are therefore
mutually orthogonal and orthogonal to $\mathbf 1$: for zero-sum $a,b$,
$\langle\sum a_i\rho_i,\sum b_\ell t_\ell\rangle=\sum_{i,\ell}a_ib_\ell=0$.
Each has dimension $n-1$, so the model space
$V=\mathop{\mathrm{span}}\mathbf 1\oplus R\oplus C\oplus T$ has dimension
$3n-2$ and its complement $(n-1)(n-2)$. The projection onto an orthogonal
direct sum is the sum of the projections (the sum lies in $V$ and the
remainder is orthogonal to each summand), so Pythagoras splits
$\|y-\bar y\mathbf 1\|^2$ into the four sums of squares with the stated
dimensions. For treatments $a\ne b$, the treatment means satisfy
$\mathbb E(\bar y_a-\bar y_b)=\tau_a-\tau_b$, because each treatment meets
every row and every column once; $\bar y_a-\bar y_b=u^\top y$ with
$u=(t_a-t_b)/n\in T\subset V$, so by 105.1 it is the least-squares estimator
($Pu=u$), with variance $\sigma^2\|u\|^2=2\sigma^2/n$. Only uncorrelated
homoscedastic errors are used; $n\ge3$ ensures a positive residual
dimension.

*Orthogonal arrays.* Given $k$ mutually orthogonal Latin squares $L_m$ of
order $s$, list the $s^2$ cells $(i,j)$ as rows with entries
$(i,j,L_1(i,j),\ldots,L_k(i,j))$. Each pair of columns shows every ordered
pair of symbols exactly once: for the first two columns since the rows are
the cells, for a coordinate and a square by the Latin property, and for two
squares by orthogonality. Conversely, in a strength-$2$ array with $s^2$ rows
the first two columns index the cells bijectively, and the remaining columns
define squares that are Latin and pairwise orthogonal by the same
correspondence.

*Bound.* Relabel the symbols of each square, which preserves the Latin
property and orthogonality, so that its first row is $(1,2,\ldots,s)$. For
$s\ge2$, the entries $L_m(2,1)$ differ from $L_m(1,1)=1$ (column $1$), and
$L_m(2,1)\ne L_{m'}(2,1)$ for $m\ne m'$, because the pair $(x,x)$ already
occurs in row $1$, column $x$, of the superposition of $L_m$ and $L_{m'}$.
Hence the $k$ values are distinct elements of $\{2,\ldots,s\}$ and
$k\le s-1$.

*Construction.* If $s=q$ is a prime power, let $F$ be a field with $q$
elements and, for $a\in F^\times$, $L_a(x,y)=ax+y$ on $F\times F$. Each
$L_a$ is Latin because $y\mapsto ax+y$ and $x\mapsto ax+y$ are bijections
($a\ne0$), and for $a\ne b$ the system $ax+y=u$, $bx+y=w$ has the unique
solution $x=(u-w)/(a-b)$, $y=u-ax$; so the $q-1$ squares are mutually
orthogonal.

**Library results.** `GaloisField` and `GaloisField.card` in
`Mathlib/FieldTheory/Finite/GaloisField.lean`;
`Submodule.eq_starProjection_of_mem_of_inner_eq_zero` and
`Submodule.norm_sq_eq_add_norm_sq_starProjection` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`; the results
listed for 105.1.

### 105.72. Horvitz–Thompson estimation and design variance

**Statement.** Let a sampling design be a probability law on subsets $s$
of $U=\{1,\ldots,N\}$, and let $y_i$ be fixed real population values.
Put $I_i=1_{\{i\in s\}}$, $\pi_i=\mathbb E I_i>0$,
$\pi_{ij}=\mathbb E I_iI_j$, $\pi_{ii}=\pi_i$, and
$\Delta_{ij}=\pi_{ij}-\pi_i\pi_j$. The Horvitz–Thompson estimator
$\hat t_y=\sum_{i\in s}y_i/\pi_i$ is unbiased for $\sum_i y_i$, with
variance $\sum_{i,j}\Delta_{ij}y_i y_j/(\pi_i\pi_j)$. If all distinct
pairs have $\pi_{ij}>0$, the sample sum
$\hat V=\sum_{i,j\in s}(\Delta_{ij}/\pi_{ij})y_i y_j/(\pi_i\pi_j)$ is
unbiased for that variance. For fixed sample size, the variance and,
assuming positive pairwise inclusion, its unbiased estimator have the
Sen–Yates–Grundy forms
$-\tfrac12\sum_{i,j\in U}\Delta_{ij}(y_i/\pi_i-y_j/\pi_j)^2$ and
$-\tfrac12\sum_{i,j\in s}(\Delta_{ij}/\pi_{ij})(y_i/\pi_i-y_j/\pi_j)^2$.
The latter is nonnegative when $\Delta_{ij}\le0$ for distinct pairs.
Positive pairwise inclusion is required for the variance estimators.
These formulas are absent from all three libraries.

**Argument.** Define the design on the finite type of subsets and put
$z_i=y_i/\pi_i$. Since $I_i^2=I_i$, the indicator moments give
$\mathbb E I_i=\pi_i$ and $\mathop{\mathrm{Cov}}(I_i,I_j)=\Delta_{ij}$.
Linearity and the variance-of-a-sum identity yield
$\mathbb E\sum_iI_iz_i=\sum_i y_i$ and
$\mathop{\mathrm{Var}}(\sum_iI_iz_i)=\sum_{i,j}\Delta_{ij}z_i z_j$.
Taking expectations term by term in $\hat V$ cancels each positive
$\pi_{ij}$, proving unbiasedness. No independence is needed.

For fixed sample size $\sum_jI_j=n$, so
$\sum_j\Delta_{ij}=\mathop{\mathrm{Cov}}(I_i,n)=0$. Symmetry gives
zero column sums as well. Expanding the squared differences therefore
shows
$$-\frac12\sum_{i,j}\Delta_{ij}(z_i-z_j)^2
=\sum_{i,j}\Delta_{ij}z_i z_j.$$
The sample version is unbiased by the same inclusion-probability
cancellation. Its diagonal terms vanish and its other terms are
nonnegative when $\Delta_{ij}\le0$. If some $\pi_{ij}=0$, cancellation
for that pair is unavailable; it is not needed for unbiasedness of the
total estimator.

**Library results.** `MeasureTheory.integral_finsetSum` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`;
`MeasureTheory.integral_indicator` in
`Mathlib/MeasureTheory/Integral/Bochner/Set.lean`;
`ProbabilityTheory.variance_sum` in
`Mathlib/Probability/Moments/Variance.lean`; finite-sum algebra.

### 105.73. Simple and stratified random sampling; Neyman allocation

**Statement.** For a uniform subset of size $1\le n\le N$ from $N\ge2$
fixed real values, the sample mean is unbiased for the population mean
and has variance $(1-n/N)S^2/n$, with $S^2$ the population variance of
divisor $N-1$. For independent uniform samples of sizes $1\le n_h\le N_h$
from strata of sizes $N_h\ge2$, the weighted mean $\sum_hW_h\bar y_{s,h}$,
$W_h=N_h/N$, is unbiased and has variance
$\sum_hW_h^2(1-n_h/N_h)S_h^2/n_h$. If $n_h\ge2$, substitution of the
sample variances of divisor $n_h-1$ gives an unbiased variance estimator.
For $S_h>0$ and fixed total $n$, the continuous allocation minimizing
variance is $n_h=nN_hS_h/\sum_lN_lS_l$, provided it satisfies the sampling
bounds; integer allocation is a separate discrete problem. These
statistical formulas are absent from all three libraries.

**Argument.** Counting subsets of size $n$ gives
$\pi_i=n/N$ and $\pi_{ij}=n(n-1)/(N(N-1))$ for $i\ne j$. Substitute in
105.72 and divide the total estimator by $N$. Equivalently, center the
values $z_i=y_i-\bar y$, so $\sum_i z_i=0$ and
$\sum_{i\ne j}z_i z_j=-\sum_i z_i^2$; the covariance sum is then
$(1-n/N)S^2/n$. This also covers $n=1$ and $n=N$.
For $n\ge2$, the identity
$$s^2=\frac1{2n(n-1)}\sum_{i,j\in s}(y_i-y_j)^2$$
and the pairwise inclusion probability show $\mathbb E s^2=S^2$.
Independent strata have zero cross-covariances, so summing their weighted
variances gives the formula and the unbiased variance estimate.

The allocation-dependent term is $\sum_h (W_hS_h)^2/n_h$; the
finite-population correction $-\sum_hW_h^2S_h^2/N_h$ is constant.
Cauchy–Schwarz gives
$$(\sum_hW_hS_h)^2\le (\sum_hn_h)
\sum_h\frac{(W_hS_h)^2}{n_h},$$
with equality precisely when $n_h$ is proportional to $W_hS_h$.
The stated allocation follows. If it violates a stratum size bound,
that unconstrained solution is not feasible and is not asserted optimal
for the constrained problem.

**Library results.** `ProbabilityTheory.uniformOn` in
`Mathlib/Probability/UniformOn.lean`; `Finset.card_powersetCard` in
`Mathlib/Data/Finset/Powerset.lean`;
`ProbabilityTheory.variance_sum` and `ProbabilityTheory.IndepFun.variance_sum`
in `Mathlib/Probability/Moments/Variance.lean`; the finite
Cauchy–Schwarz inequality. `TauCeti.Probability.sampleWithoutReplacement`
in `TauCeti/Probability/PopulationSampling/Finite.lean` gives the
same simple-random-sampling law in ordered form.

### 105.46. Neyman's theorem

**Statement.** In a completely randomized experiment,
$\mathbb E\hat\tau=\tau$ and
$$\mathop{\mathrm{Var}}(\hat\tau)
=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}{n}.$$
The estimator $\hat V=\hat S^2(1)/n_1+\hat S^2(0)/n_0$ satisfies
$\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)=S^2(\tau)/n\ge0$, with
equality if and only if all $\tau_i$ are equal. TauCeti defines sampling
without replacement, and Statlib's potential-response notation expresses the
observed outcomes $Y_i(A_i)$; no assignment mechanism or design-based
estimator is defined. The theorem is a finite computation from the
covariances of the treatment indicators under that law, which are not
stated.

**Argument.** Take the treated set uniform on the subsets of size $n_1$ of
$\{1,\ldots,n\}$, with $n_1,n_0\ge1$ for $\hat\tau$ and $n_1,n_0\ge2$ for
$\hat V$; let $W_i$ be the treatment indicators. Counting subsets gives
$\mathbb EW_i=n_1/n$ and, for $i\ne j$,
$\mathbb E W_iW_j=n_1(n_1-1)/(n(n-1))$, hence
$\mathop{\mathrm{Var}}W_i=n_1n_0/n^2$ and
$\mathop{\mathrm{Cov}}(W_i,W_j)=-n_1n_0/(n^2(n-1))$. For fixed numbers
$c_i$ with mean $\bar c$ and $S_c^2=\sum_i(c_i-\bar c)^2/(n-1)$, this gives
$$
\mathbb E\frac1{n_1}\sum_iW_ic_i=\bar c,\qquad
\mathop{\mathrm{Var}}\Bigl(\sum_iW_ic_i\Bigr)=\frac{n_1n_0}n\,S_c^2 .
$$
Write $\hat\tau=\sum_iW_ia_i-\sum_iY_i(0)/n_0$ with
$a_i=Y_i(1)/n_1+Y_i(0)/n_0$. Unbiasedness follows from the first identity
applied to both arms. For the variance, expand
$S_a^2=S^2(1)/n_1^2+S^2(0)/n_0^2+2S(1,0)/(n_1n_0)$, with $S(1,0)$ the
finite-population covariance, and use
$S^2(\tau)=S^2(1)+S^2(0)-2S(1,0)$ and $n_0/n=1-n_1/n$:
$$
\frac{n_1n_0}nS_a^2=\frac{S^2(1)}{n_1}-\frac{S^2(1)}n
+\frac{S^2(0)}{n_0}-\frac{S^2(0)}n+\frac{2S(1,0)}n
=\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}n .
$$
Within each arm the sample is a simple random sample, and the second-moment
identities give $\mathbb E\hat S^2(a)=S^2(a)$ (unbiasedness of the sample
variance without replacement, which needs $n_a\ge2$); hence
$\mathbb E\hat V-\mathop{\mathrm{Var}}\hat\tau=S^2(\tau)/n\ge0$, and
$S^2(\tau)=0$ exactly when all $\tau_i$ are equal.

**Library results.** `ProbabilityTheory.uniformOn` in
`Mathlib/Probability/UniformOn.lean`; `Finset.card_powersetCard` in
`Mathlib/Data/Finset/Powerset.lean`;
`ProbabilityTheory.variance_sum` in `Mathlib/Probability/Moments/Variance.lean`.
TauCeti's `TauCeti.Probability.sampleWithoutReplacement`
(`TauCeti/Probability/PopulationSampling/Finite.lean`) is an equivalent
formulation of the design, after transport from ordered to unordered
samples. Statlib's `PotentialResponse` and `PotentialResponse.select`
(`Statlib/Causal/PotentialResponse.lean`) supply the notation for the
potential and observed outcomes.

### 105.47. Identification by regression and by weighting

**Statement.** Under conditional ignorability and positivity at level $a$,
and if $\mathbb E|Y(a)|<\infty$,
$$\mathbb E[Y(a)]=\mathbb E[m_a(X)]
=\mathbb E\Bigl[\frac{1_{\{A=a\}}Y}{e_a(X)}\Bigr],$$
so for binary treatment $\theta=\mathbb E[m_1(X)-m_0(X)]$ when the
hypotheses hold at both levels. Statlib's potential-response notation gives
$Y(a)$ and the observed outcome under consistency, but no potential-outcome
model with a probability structure is defined in any of the three
libraries. The identities follow by a short argument from Mathlib's
conditional independence and conditional expectation.

**Argument.** Formalize ignorability as conditional independence of
$\sigma(Y(a))$ and $\sigma(A)$ given $\sigma(X)$, and consistency as
$1_{\{A=a\}}Y=1_{\{A=a\}}Y(a)$. Let $H=\{A=a\}$,
$e_a(X)=\mathbb E[1_H\mid X]\ge\delta$, and define
$m_a(X)=\mathbb E[1_HY\mid X]/e_a(X)$, a version of
$\mathbb E[Y\mid A=a,X]$. By TauCeti's projection lemma for conditional
independence, $\mathbb E[1_H\mid\sigma(Y(a))\vee\sigma(X)]=e_a(X)$. The
tower property and the pull-out property for the
$\sigma(Y(a))\vee\sigma(X)$-measurable integrable factor $Y(a)$ then give
$$
\mathbb E[1_HY(a)\mid X]
=\mathbb E\bigl[Y(a)\,\mathbb E[1_H\mid\sigma(Y(a))\vee\sigma(X)]\bigm|X\bigr]
=e_a(X)\,\mathbb E[Y(a)\mid X].
$$
Hence $m_a(X)=\mathbb E[Y(a)\mid X]$, and taking expectations gives the
regression formula. For the weighting formula, $1/e_a(X)\le1/\delta$ is
bounded and $\sigma(X)$-measurable, so
$\mathbb E[1_HY/e_a(X)]=\mathbb E[\mathbb E[1_HY(a)\mid X]/e_a(X)]
=\mathbb E[\mathbb E[Y(a)\mid X]]=\mathbb EY(a)$. Subtract the two levels
for $\theta$. The TauCeti lemma is stated on a standard Borel sample space;
otherwise one transports to the joint law of $(X,A,Y(a))$.

**Library results.** `TauCeti.Probability.condExp_indicator_sup_eq_of_condIndep`
in `TauCeti/Probability/Independence/Conditional.lean`;
`MeasureTheory.condExp_condExp_of_le` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`;
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean`;
`ProbabilityTheory.CondIndep` and `ProbabilityTheory.condIndep_iff` in
`Mathlib/Probability/Independence/Conditional.lean`.

### 105.48. Propensity score

**Statement.** Under conditional ignorability, $Y(a)$ is conditionally
independent of $A$ given $e(X)$. The propensity score is a balancing score,
and it is a function of every balancing score. This follows by a short
argument from Mathlib's conditional expectation; it is not stated in any of
the three libraries.

**Argument.** Let $A$ be binary, $H=\{A=1\}$ and
$e(X)=\mathbb E[1_H\mid X]$; by Doob–Dynkin it is a measurable function of
$X$, so $\sigma(e(X))\subset\sigma(X)$. For binary $A$, the drop-information
criterion of TauCeti reduces conditional independence of $\sigma(A)$ and
$\mathcal F$ given $\mathcal G$ to the identity
$\mathbb E[1_H\mid\mathcal F\vee\mathcal G]=\mathbb E[1_H\mid\mathcal G]$
(the other sets in $\sigma(A)$ are $\varnothing$, $H^c$ and $\Omega$).

By ignorability and TauCeti's projection lemma,
$\mathbb E[1_H\mid\sigma(Y(a))\vee\sigma(X)]=e(X)$. Since
$\sigma(Y(a))\vee\sigma(e(X))\subset\sigma(Y(a))\vee\sigma(X)$ and $e(X)$
is measurable for the smaller $\sigma$-algebra, the tower property gives
$\mathbb E[1_H\mid\sigma(Y(a))\vee\sigma(e(X))]=e(X)$, and similarly
$\mathbb E[1_H\mid e(X)]=e(X)$; so $Y(a)$ and $A$ are conditionally
independent given $e(X)$. The same computation with $\sigma(X)$ in place of
$\sigma(Y(a))$ (no hypothesis needed) shows $A\perp X\mid e(X)$, i.e. $e$ is
a balancing score. If $b(X)$ is a balancing score, the projection lemma for
$A\perp X\mid b(X)$ gives
$e(X)=\mathbb E[1_H\mid\sigma(X)\vee\sigma(b(X))]=\mathbb E[1_H\mid b(X)]$
almost surely, and the right side is $\sigma(b(X))$-measurable, hence of the
form $g(b(X))$ with $g$ measurable. The conclusion "is a function of" holds
almost surely, as it must for objects defined up to null sets. As in 105.47,
the TauCeti lemmas assume a standard Borel sample space.

**Library results.** `TauCeti.Probability.condIndep_of_indicator_condExp_eq`
and `TauCeti.Probability.condExp_indicator_sup_eq_of_condIndep` in
`TauCeti/Probability/Independence/Conditional.lean`;
`MeasureTheory.condExp_condExp_of_le` and
`MeasureTheory.condExp_of_stronglyMeasurable` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`;
`MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp` in
`Mathlib/MeasureTheory/Function/FactorsThrough.lean`.

### 105.50. Local average treatment effect

**Statement.** If $(Y(0),Y(1),A(0),A(1))$ is independent of $Z$, exclusion
and monotonicity hold, and $P(A=1\mid Z=1)\ne P(A=1\mid Z=0)$, then
$$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
{\mathbb E[A\mid Z=1]-\mathbb E[A\mid Z=0]}
=\mathbb E\bigl[Y(1)-Y(0)\mid A(1)>A(0)\bigr].$$
Not stated in any of the three libraries. It follows by a short computation
from independence.

**Argument.** Assume $Y(0),Y(1)$ integrable, $A(z)\in\{0,1\}$, and
$0<P(Z=1)<1$ so that the conditional expectations are defined. By
exclusion the observed outcome is
$Y=Y(0)+A(Z)(Y(1)-Y(0))$ and $A=A(Z)$. Put $U=(Y(0),Y(1),A(0),A(1))$. For
$z\in\{0,1\}$, $1_{\{Z=z\}}Y=1_{\{Z=z\}}g_z(U)$ with
$g_z(U)=Y(0)+A(z)(Y(1)-Y(0))$, and independence of $U$ and $Z$ gives
$\mathbb E[1_{\{Z=z\}}g_z(U)]=P(Z=z)\,\mathbb Eg_z(U)$, so
$\mathbb E[Y\mid Z=z]=\mathbb Eg_z(U)$ and likewise
$\mathbb E[A\mid Z=z]=\mathbb EA(z)$. Therefore the numerator is
$\mathbb E[(A(1)-A(0))(Y(1)-Y(0))]$ and the denominator
$\mathbb E[A(1)-A(0)]$. Monotonicity makes $A(1)-A(0)$ the indicator of
$\{A(1)>A(0)\}$, so the denominator is the (nonzero, by hypothesis)
probability of compliers, and the ratio is the conditional expectation on
that event.

**Library results.** `ProbabilityTheory.IndepFun.integral_comp_mul_comp` in
`Mathlib/Probability/Independence/Integration.lean`; `ProbabilityTheory.cond`
in `Mathlib/Probability/ConditionalProbability.lean`.

## 106. Dependent data and stochastic models

### 106.12. Long-run variance of a sample mean

**Statement.** For a stationary process with absolutely summable
autocovariances, $n\mathop{\mathrm{Var}}(\bar X_n)\to v=\sum_h\gamma(h)=2\pi
f(0)$. For a linear process
$X_t-\mu=\sum_{j\ge0}\psi_j\varepsilon_{t-j}$ with absolutely summable
coefficients and independent identically distributed innovations of mean
zero and finite variance $\sigma^2$, $\sqrt n(\bar X_n-\mu)\Rightarrow N(0,v)$
with $v=\sigma^2(\sum_j\psi_j)^2$; if $v>0$ and $\hat v_n\to_Pv$, the interval
$\bar X_n\pm z(\hat v_n/n)^{1/2}$ has asymptotic coverage $1-\alpha$.
Mathlib's variance of a finite sum as a double sum of covariances gives the
first statement by reindexing and dominated convergence, which are not
carried out; the central limit theorem for linear processes is missing.

**Scope.** The argument gives the first sentence. The central limit theorem
for linear processes, and the coverage statement that rests on it, remain a
gap.

**Argument.** By the double-sum formula and stationarity,
$$
n\mathop{\mathrm{Var}}(\bar X_n)=\frac1n\sum_{s,t=1}^n\gamma(s-t)
=\sum_{|h|<n}\Bigl(1-\frac{|h|}n\Bigr)\gamma(h),
$$
since the difference $s-t=h$ occurs $n-|h|$ times. The summands, extended by
$0$ for $|h|\ge n$, converge to $\gamma(h)$ for each $h$ and are dominated by
the summable $|\gamma(h)|$, so Tannery's theorem gives convergence to
$\sum_h\gamma(h)$. The equality $\sum_h\gamma(h)=2\pi f(0)$ is the definition
of $f$ at $0$, the series converging absolutely. Square integrability of
each $X_t$ is part of the hypothesis.

**Library results.** `ProbabilityTheory.variance_sum` in
`Mathlib/Probability/Moments/Variance.lean`;
`ProbabilityTheory.covariance_sum_sum` in
`Mathlib/Probability/Moments/Covariance.lean`;
`tendsto_tsum_of_dominated_convergence` in
`Mathlib/Analysis/Normed/Group/Tannery.lean`.

### 106.14. Herglotz theorem and rational spectral densities

**Statement.** A complex function $\gamma$ on $\mathbb Z$ is the
autocovariance function of a weakly stationary (complex-valued) process if
and only if it is Hermitian and nonnegative definite, and if and only if
$\gamma(h)=\int_{(-\pi,\pi]}e^{ih\nu}\,dF(\nu)$ for a right-continuous,
nondecreasing, bounded $F$ on $[-\pi,\pi]$ with $F(-\pi)=0$; $F$ is uniquely
determined by $\gamma$. If $\sum_h|\gamma(h)|<\infty$, then $F$ has the
continuous density $f$. If $\varphi$ and $\theta$ have no common zeros and
$\varphi$ has no zero on the unit circle, the ARMA equation has a unique
stationary solution, with spectral density
$$f(\lambda)=\frac{\sigma^2}{2\pi}\,
\frac{|\theta(e^{-i\lambda})|^2}{|\varphi(e^{-i\lambda})|^2}.$$
TauCeti proves Herglotz's equivalence between positive definiteness on
$\mathbb Z$ and representation by a finite positive measure on the unit
circle, and realizes positive-definite kernels as Gram kernels in a Hilbert
space. Missing are the realization as the autocovariance of a stationary
process (for instance a Gaussian one, through Mathlib's projective limit of
finite-dimensional laws, or a random-phase process), the density for
summable $\gamma$, and the ARMA statement; uniqueness follows from
TauCeti's injectivity of the Fourier–Stieltjes transform on Pontryagin duals
but is not stated.

**Scope.** The argument covers the three-way equivalence, the uniqueness of
$F$, and the continuous density for summable $\gamma$. The ARMA existence,
uniqueness and spectral density remain a gap.

**Argument.** *Autocovariance implies positive definite.* With
$\gamma(h)=\mathbb E[(X_{t+h}-m)\overline{(X_t-m)}]$,
$$
\sum_{r,s}a_r\overline{a_s}\,\gamma(r-s)
=\mathbb E\Bigl|\sum_ra_r(X_r-m)\Bigr|^2\ge0 .
$$
Nonnegative definiteness in TauCeti's sense (the double sum is a nonnegative
real) already implies the Hermitian property, by taking two-point families.

*Positive definite implies the representation.* TauCeti's Herglotz theorem
gives a finite measure $\mu$ on the circle with
$\gamma(h)=\int z^h\,d\mu(z)$. Transport $\mu$ to $(-\pi,\pi]$ along
$\nu\mapsto e^{i\nu}$ (a measurable bijection onto the circle) and put
$F(x)=\mu\{e^{i\nu}:-\pi<\nu\le x\}$; it is right-continuous,
nondecreasing, bounded, with $F(-\pi)=0$.

*Representation implies autocovariance.* Given $F$ with total mass
$c=F(\pi)=\gamma(0)$, take independent $U\sim F/c$ on $(-\pi,\pi]$ and
$\Theta$ uniform on $(-\pi,\pi]$ (if $c=0$, take $X\equiv0$), and set
$X_t=\sqrt c\,e^{i(tU+\Theta)}$. Then $\mathbb EX_t=0$ because
$\mathbb Ee^{i\Theta}=0$, and
$\mathbb E X_{t+h}\overline{X_t}=c\,\mathbb Ee^{ihU}=\gamma(h)$, so $X$ is a
weakly stationary process with autocovariance $\gamma$.

*Uniqueness.* Two finite measures on the circle with the same moments
$\int z^h$ have the same Fourier–Stieltjes transform on $\mathbb Z$ after
transport along TauCeti's identification of the circle with the dual of
$\mathbb Z$; TauCeti's uniqueness theorem on Polish duals gives equality, and
$F$ is determined by the measure.

*Density.* If $\sum_h|\gamma(h)|<\infty$, the series
$f(\nu)=(2\pi)^{-1}\sum_h\gamma(h)e^{-ih\nu}$ converges uniformly, so $f$ is
continuous. It is nonnegative: the Fejér means
$$
\frac1{2\pi N}\sum_{r,s=0}^{N-1}\gamma(r-s)e^{-i(r-s)\nu}
=\frac1{2\pi}\sum_{|h|<N}\Bigl(1-\frac{|h|}N\Bigr)\gamma(h)e^{-ih\nu}
$$
are nonnegative by positive definiteness (coefficients $e^{-ir\nu}$) and
converge to $f(\nu)$ by dominated convergence for series. Termwise
integration and orthogonality of the exponentials give
$\int_{-\pi}^{\pi}e^{ih\nu}f(\nu)\,d\nu=\gamma(h)$, so the finite measure
$f(\nu)\,d\nu$ has the moments of $\gamma$, and by uniqueness it is $dF$.

**Library results.** `TauCeti.exists_isFiniteMeasure_integral_zpow_eq` and
`TauCeti.isPositiveDefiniteSub_iff_exists_isFiniteMeasure_integral_zpow_eq`
in `TauCeti/Analysis/Bochner/Herglotz.lean`;
`MeasureTheory.FiniteMeasure.pontryaginMeasureTransform_map_circleEquivPontryaginDualInt`
in the same file; `MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq`
in `TauCeti/Analysis/Fourier/Pontryagin/Uniqueness.lean`;
`TauCeti.IsPositiveDefiniteSub` in
`TauCeti/Analysis/PositiveDefinite/AddGroup.lean`; `continuous_tsum` in
`Mathlib/Analysis/Normed/Group/FunctionSeries.lean`;
`tendsto_tsum_of_dominated_convergence` in
`Mathlib/Analysis/Normed/Group/Tannery.lean`;
`MeasureTheory.integral_tsum_of_summable_integral_norm` in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`; orthogonality of
the Fourier basis in `Mathlib/Analysis/Fourier/AddCircle.lean`.

### 106.18. Stationarity of GARCH$(1,1)$

**Statement.** Let
$\gamma=\mathbb E\log(\beta_1+\alpha_1\varepsilon_0^2)\in[-\infty,\infty)$. If
$\gamma<0$, the series
$$\sigma_t^2=\alpha_0\Bigl(1+\sum_{n=1}^\infty\prod_{j=1}^n
(\beta_1+\alpha_1\varepsilon_{t-j}^2)\Bigr)$$
converges almost surely and, with $X_t=\sigma_t\varepsilon_t$, defines the
unique strictly stationary solution; if $\gamma\ge0$, there is no strictly
stationary solution. A nonanticipative weakly stationary solution with
finite second moments exists if and only if $\alpha_1+\beta_1<1$; it is then
the solution above, and $(X_t)$ is weak white noise of variance
$\alpha_0/(1-\alpha_1-\beta_1)$. Absent from all three libraries.
Because the innovations are independent, the almost-sure convergence and
uniqueness need only Mathlib's strong law for independent identically
distributed variables; nonexistence in the boundary case $\gamma=0$ needs
the oscillation of a nondegenerate mean-zero random walk, which none of the
three libraries proves.

**Scope.** The argument covers everything except nonexistence in the
boundary case $\gamma=0$ when $\log(\beta_1+\alpha_1\varepsilon_0^2)$ is not
almost surely constant; that case needs the oscillation of a
nondegenerate mean-zero random walk ($\limsup_nS_n=+\infty$ almost surely),
which none of the three libraries proves, and remains a gap.

**Argument.** Write $a_s=\beta_1+\alpha_1\varepsilon_s^2$ and
$\Pi_{t,n}=\prod_{j=1}^na_{t-j}$. For fixed $t$ the variables
$Y_j=\log a_{t-j}$, $j\ge1$, are independent and identically distributed with
values in $[-\infty,\infty)$, and $Y_j^+\le a_{t-j}$ is integrable because
$\mathbb E\varepsilon^2=1$. The strong law of large numbers is needed only
for independent identically distributed summands.

*Convergence for $\gamma<0$.* If $\gamma>-\infty$, the strong law gives
$n^{-1}\log\Pi_{t,n}\to\gamma$ almost surely; if $\gamma=-\infty$, apply it to
$\max(Y_j,-K)$, whose mean is negative for large $K$ by monotone
convergence. In both cases $\Pi_{t,n}\le\rho^n$ eventually for some
$\rho<1$, and the series converges by comparison with a geometric series.

*Solution and stationarity.* Multiplying the series for $\sigma_{t-1}^2$ by
$a_{t-1}$ shifts the products by one index, so
$\sigma_t^2=\alpha_0+a_{t-1}\sigma_{t-1}^2
=\alpha_0+\alpha_1X_{t-1}^2+\beta_1\sigma_{t-1}^2$. Since
$\sigma_t^2=g((\varepsilon_{t-j})_{j\ge1})$ for one measurable $g$, and the
law of an independent identically distributed sequence is shift invariant,
$(\sigma_t,\varepsilon_t)$ is strictly stationary; $\sigma_t^2$ depends only
on $\varepsilon_s$, $s<t$, so the solution is nonanticipative.

*Uniqueness.* For any solution, iteration gives
$$
\sigma_t^2=\alpha_0\Bigl(1+\sum_{n=1}^N\Pi_{t,n}\Bigr)
+\Pi_{t,N+1}\,\sigma_{t-N-1}^2 .
$$
If the $\sigma_s^2$ are identically distributed (as for a strictly stationary
solution), the remainder tends to $0$ in probability, since $\Pi_{t,N+1}\to0$
almost surely and the law of $\sigma_{t-N-1}^2$ does not depend on $N$.
Hence $\sigma_t^2$ equals the series almost surely.

*Nonexistence for $\gamma>0$.* Then $\gamma$ is finite, the strong law gives
$\Pi_{t,n}\to\infty$ almost surely, and every solution satisfies
$\sigma_t^2\ge\alpha_0\Pi_{t,n}$ for all $n$, which is impossible for a
finite $\sigma_t^2$. If $\gamma=0$ and $Y$ is almost surely $0$, the
products equal $1$ and the same bound gives $\sigma_t^2=\infty$.

*Second-order stationarity.* If $\alpha_1+\beta_1<1$, Jensen gives
$\gamma\le\log\mathbb Ea_0=\log(\alpha_1+\beta_1)<0$, so the solution above
exists; independence gives $\mathbb E\Pi_{t,n}=(\alpha_1+\beta_1)^n$, and
monotone convergence gives
$\mathbb E\sigma_t^2=\alpha_0/(1-\alpha_1-\beta_1)$. Then
$\mathbb EX_t^2=\mathbb E\sigma_t^2$, $\mathbb EX_t=0$, and for $h\ge1$,
$\mathbb EX_tX_{t+h}=\mathbb E[\sigma_t\varepsilon_t\sigma_{t+h}]\,
\mathbb E\varepsilon_{t+h}=0$, because $\varepsilon_{t+h}$ is independent of
the integrable product $\sigma_t\varepsilon_t\sigma_{t+h}$, a function of
$\varepsilon_s$, $s<t+h$. So $(X_t)$ is weak white noise of the stated
variance. Conversely, let a nonanticipative solution have
$c=\mathbb EX_t^2=\mathbb E\sigma_t^2<\infty$ constant in $t$. Taking
expectations in the recursion, using $\varepsilon_{t-1}$ independent of
$\sigma_{t-1}^2$, gives $c=\alpha_0+(\alpha_1+\beta_1)c$, so
$\alpha_1+\beta_1<1$ since $\alpha_0>0$. Moreover
$a_s=(\sigma_{s+1}^2-\alpha_0)/\sigma_s^2$ (note $\sigma_s^2\ge\alpha_0$), so
$\prod_{j=2}^{N+1}a_{t-j}\,\sigma_{t-N-1}^2$ is a function of
$\{\sigma_s^2:s\le t-1\}$, which is independent of $\varepsilon_{t-1}$,
and similarly at each lower index; peeling off one factor at a time
(nonnegative integrands, so no integrability issue) gives
$\mathbb E[\Pi_{t,N+1}\sigma_{t-N-1}^2]=(\alpha_1+\beta_1)^{N+1}c\to0$. The
remainder in the iteration therefore tends to $0$ in $L^1$, and the
solution is the series above.

**Library results.** `ProbabilityTheory.strong_law_ae_real` in
`Mathlib/Probability/StrongLaw.lean`; `ConcaveOn.le_map_integral` in
`Mathlib/Analysis/Convex/Integral.lean`;
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` in
`Mathlib/Probability/Independence/Integration.lean`;
`MeasureTheory.lintegral_tsum` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`;
`MeasureTheory.Measure.infinitePi` in `Mathlib/Probability/ProductMeasure.lean`
for the independent identically distributed sequence.

### 106.24. Bochner's theorem and the Matérn family

**Statement.** A function $K$ on $\mathbb R^d$ is the autocovariance of a
weakly stationary, mean-square continuous, complex random field if and only
if $K(x)=\int e^{i\omega\cdot x}\,F(d\omega)$ for a finite positive measure
$F$. On $\mathbb R$ the field is $m$ times mean-square differentiable if and
only if $K$ has a finite derivative of order $2m$ at $0$, equivalently
$\int\omega^{2m}F(d\omega)<\infty$, and for $m=1$ the derivative has
autocovariance $-K''$. The Matérn covariance is positive definite on every
$\mathbb R^d$ with the stated spectral density, with the stated
differentiability and half-integer forms. TauCeti proves Bochner's theorem on
$\mathbb R^d$ as the equivalence between continuous positive-definite
functions and Fourier transforms of finite positive measures. Missing are the
random-field realization, the differentiability criterion, and the Matérn
family.

**Scope.** The argument gives the first sentence. The differentiability
criterion (which needs the relation between derivatives at $0$ of a
Fourier–Stieltjes transform and moments of $F$) and the Matérn statements
(whose Bessel function $\mathcal K_\nu$ is not defined in Mathlib) remain a
gap.

**Argument.** *Only if.* For a weakly stationary field with
$K(h)=\mathbb E[(X(x+h)-m)\overline{(X(x)-m)}]$,
$\sum_{j,k}c_j\overline{c_k}K(x_j-x_k)=\mathbb E|\sum_jc_j(X(x_j)-m)|^2\ge0$,
so $K$ is positive definite. By Cauchy–Schwarz,
$|K(h)-K(h')|^2\le K(0)\,\mathbb E|X(h)-X(h')|^2$, and mean-square
continuity makes the right side tend to $0$ as $h'\to h$; so $K$ is
continuous. TauCeti's Bochner theorem gives a unique finite measure $\mu$
with $K(v)=\int e^{-2\pi i\langle v,q\rangle}\,d\mu(q)$; the image of $\mu$
under $q\mapsto-2\pi q$ is the required $F$.

*If.* Given $F$ of mass $c=K(0)$, take independent $\omega\sim F/c$ and
$\Theta$ uniform on $(-\pi,\pi]$ (if $c=0$, take $X\equiv0$), and put
$X(x)=\sqrt c\,e^{i(\omega\cdot x+\Theta)}$. Then $\mathbb EX(x)=0$,
$\mathbb EX(x+h)\overline{X(x)}=c\,\mathbb Ee^{i\omega\cdot h}=K(h)$, and
$\mathbb E|X(x)-X(y)|^2=2K(0)-2\mathop{\mathrm{Re}}K(x-y)\to0$ as $y\to x$,
since $K$ is continuous by dominated convergence. So $X$ is a weakly
stationary, mean-square continuous field with autocovariance $K$.

**Library results.** `TauCeti.bochner_euclideanSpace` and `TauCeti.bochner`
in `TauCeti/Analysis/Bochner/BochnerTheorem.lean`; `TauCeti.fourierAtom` in
`TauCeti/Analysis/PositiveDefinite/FourierAtom.lean`;
`TauCeti.IsPositiveDefiniteSub` in
`TauCeti/Analysis/PositiveDefinite/AddGroup.lean`; product measures and
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` in
`Mathlib/Probability/Independence/Integration.lean`;
`MeasureTheory.tendsto_integral_of_dominated_convergence` in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`.

### 106.37. Sequential probability ratio test

**Statement.** Let the observations be independent with density $f_i$ under
$\mathbb P_i$, and suppose $0<\mathbb E_i|\log(f_1/f_0)|<\infty$ and
$\mathbb P_i(f_1\ne f_0)>0$ for $i=0,1$. Then $\mathbb E_iN<\infty$ and, by
Wald's identity,
$\mathbb E_iN=\mathbb E_i\log\Lambda_N/\mathbb E_i\log(f_1/f_0)$. With
$\alpha=\mathbb P_0(\text{reject }H_0)$ and
$\beta=\mathbb P_1(\text{accept }H_0)$,
$$B\le\frac{1-\beta}\alpha,\qquad A\ge\frac\beta{1-\alpha}.$$
Among all tests with type I error at most $\alpha$ and type II error at most
$\beta$, the test minimizes both $\mathbb E_0N$ and $\mathbb E_1N$ (Wald and
Wolfowitz). Mathlib's optional sampling covers only bounded stopping times.
Statlib proves Wald's identity for integrable stopping times of independent
identically distributed sequences, the likelihood-ratio density of the laws
stopped at a stopping time, and the identity
$\mathbb E_\mu[N]\,\mathrm{KL}(\mu,\nu)$ for the Kullback–Leibler divergence
of the stopped laws, which supplies the information lower bound used for the
optimality. No sequential test is defined in any of the three libraries; the
finiteness of $\mathbb E_iN$, the error bounds, and the Wald–Wolfowitz
optimality are absent.

**Scope.** The argument covers finiteness of $\mathbb E_iN$, Wald's identity,
and Wald's inequalities. The Wald–Wolfowitz optimality, which needs
optimal-stopping theory, remains a gap.

**Argument.** Model the observations by the countable product
$\mathbb P_i=(f_i\,dx)^{\otimes\mathbb N}$. Write $Z_k=\log(f_1/f_0)(X_k)$,
$S_n=\sum_{k\le n}Z_k=\log\Lambda_n$, and $c=\log B-\log A>0$. The
integrability hypothesis gives $f_0,f_1>0$ almost surely under both laws,
so $\Lambda_n\in(0,\infty)$ almost surely.

*Finiteness of $\mathbb E_iN$.* Since $\mathbb P_i(Z\ne0)>0$, there are
$\eta>0$ and a sign $\epsilon$ with $\mathbb P_i(\epsilon Z>\eta)=p>0$.
Choose $m$ with $m\eta>c$. On $\{N>km\}$ all partial sums lie in
$(\log A,\log B)$, so each of the $k$ disjoint block sums
$S_{jm}-S_{(j-1)m}$ has absolute value less than $c$; these block events are
independent, each of probability at most $1-p^m$. Hence
$\mathbb P_i(N>km)\le(1-p^m)^k$, and $N$ has geometric tails, so
$\mathbb E_iN<\infty$.

*Wald's identity.* $S_N=\sum_k Z_k1_{\{N\ge k\}}$ and $\{N\ge k\}$ is
determined by $X_1,\ldots,X_{k-1}$, hence independent of $Z_k$, so
$\mathbb E_i[Z_k;N\ge k]=\mathbb P_i(N\ge k)\,\mathbb E_iZ$, and
$\sum_k\mathbb E_i[|Z_k|;N\ge k]=\mathbb E_i|Z|\,\mathbb E_iN<\infty$. These
are the hypotheses of Statlib's general form of Wald's identity, applied in
its indexing from $0$ to the random time $N-1$ (set to $0$ on the null event
$\{N=\infty\}$, which changes the events $\{N\ge k\}$ only by null sets);
it gives $\mathbb E_iS_N=\mathbb E_iZ\,\mathbb E_iN$. The mean is
nonzero: $\mathbb E_1Z$ is the Kullback–Leibler divergence of the
single-observation law under $\mathbb P_1$ from that under $\mathbb P_0$
(absolute continuity holds since $f_0>0$ $\mathbb P_1$-almost surely), and
it is positive because the two laws differ; likewise
$\mathbb E_0Z=-\mathrm{KL}<0$. Dividing gives the identity.

*Wald's inequalities.* On the first $n$ coordinates the two laws are
mutually absolutely continuous with $d\mathbb P_0=\Lambda_n^{-1}d\mathbb P_1$.
The rejection event is the disjoint union over $n$ of
$\{N=n,\Lambda_n\ge B\}$, which is determined by the first $n$ coordinates;
since $N<\infty$ almost surely,
$$
\alpha=\sum_n\mathbb E_1\bigl[\Lambda_n^{-1};N=n,\Lambda_n\ge B\bigr]
\le B^{-1}\,\mathbb P_1(\text{reject})=B^{-1}(1-\beta),
$$
and in the same way
$\beta=\sum_n\mathbb E_0[\Lambda_n;N=n,\Lambda_n\le A]\le A(1-\alpha)$. If
$\alpha=0$ the first inequality is read as $B\le\infty$.

**Library results.**
`ProbabilityTheory.integral_sum_Iic_eq_integral_sum_Iic_integral` (Wald's
identity) in `Statlib/Testing/Sequential/Wald.lean`;
`MeasureTheory.Measure.infinitePi` in
`Mathlib/Probability/ProductMeasure.lean`;
`ProbabilityTheory.iIndepFun.indepFun_finset` in
`Mathlib/Probability/Independence/Basic.lean`;
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` in
`Mathlib/Probability/Independence/Integration.lean`;
`MeasureTheory.integral_tsum` in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`;
`InformationTheory.toReal_klDiv` and `InformationTheory.klDiv_eq_zero_iff`
in `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`.

### 106.38. Ville's inequality and e-values

**Statement.** If $(M_n)_{n\ge0}$ is a nonnegative supermartingale with
$M_0\le1$, then for every $\alpha\in(0,1)$,
$$\mathbb P\Bigl(\sup_{n\ge0}M_n\ge\frac1\alpha\Bigr)\le\alpha.$$
If $E_1,E_2,\ldots$ are nonnegative and adapted with
$\mathbb E[E_n\mid\mathcal F_{n-1}]\le1$ under every law in a null
hypothesis, then $M_n=E_1\cdots E_n$, $M_0=1$, is a nonnegative
supermartingale under each such law, $M_\tau$ is an e-value for every almost
surely finite stopping time $\tau$, and rejecting at the first $n$ with
$M_n\ge1/\alpha$ has level $\alpha$. Mathlib's Doob maximal inequality, which
TauCeti extends to general linearly ordered time, gives the bound for
nonnegative martingales on each finite horizon. Statlib defines e-variables
for a set of laws, with convexity, closure under $\liminf$, products for
product laws, and the existence of the numeraire e-variable. The
supermartingale case follows by a short argument; neither step, nor the
product supermartingale and the e-value consequences for running products
of conditional e-values, is stated in any of the three libraries.

**Argument.** *Ville.* Put $c=1/\alpha$ and let $\pi_n$ be the hitting time
of $[c,\infty)$ by $M$ capped at $n$, a stopping time bounded by $n$. Since
$-M$ is a submartingale, optional stopping at the bounded times $0\le\pi_n$
gives $\mathbb EM_{\pi_n}\le\mathbb EM_0\le1$. On
$\{\max_{k\le n}M_k\ge c\}$ one has $M_{\pi_n}\ge c$, and $M\ge0$, so
Markov's inequality gives $c\,\mathbb P(\max_{k\le n}M_k\ge c)\le1$. The
events increase to $\{\exists n:M_n\ge c\}$, and continuity from below
bounds its probability by $\alpha$. (This event may be smaller than
$\{\sup_nM_n\ge c\}$, on which the supremum need not be attained; apply the
bound with $c'<c$ and let $c'\uparrow c$, which gives
$\mathbb P(\sup_nM_n\ge c)\le\lim_{c'\uparrow c}1/c'=\alpha$.)

*Product supermartingale.* Assume each $E_n$ integrable. By induction,
$M_{n-1}$ is nonnegative and integrable; truncating,
$\mathbb E[(M_{n-1}\wedge K)E_n\mid\mathcal F_{n-1}]
=(M_{n-1}\wedge K)\,\mathbb E[E_n\mid\mathcal F_{n-1}]\le M_{n-1}\wedge K$
by the pull-out property, and monotone convergence in $K$ gives
integrability of $M_n$ and $\mathbb E[M_n\mid\mathcal F_{n-1}]\le M_{n-1}$.

*E-values and level.* For an almost surely finite stopping time $\tau$,
$M_{\tau\wedge n}\to M_\tau$ almost surely, and optional stopping gives
$\mathbb EM_{\tau\wedge n}\le1$; Fatou's lemma gives $\mathbb EM_\tau\le1$,
so $M_\tau$ is an e-variable for the null hypothesis in Statlib's sense.
The rejection event $\{\exists n:M_n\ge1/\alpha\}$ has probability at most
$\alpha$ by Ville, under each law of the null hypothesis separately.

**Library results.** `MeasureTheory.Submartingale.expected_stoppedValue_mono`
in `Mathlib/Probability/Martingale/OptionalStopping.lean`;
`MeasureTheory.Supermartingale.neg` in
`Mathlib/Probability/Martingale/Basic.lean`; `MeasureTheory.hittingBtwn` and
`MeasureTheory.Adapted.isStoppingTime_hittingBtwn` in
`Mathlib/Probability/Process/HittingTime.lean`;
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left` in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean`;
`MeasureTheory.lintegral_liminf_le` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`;
`MeasureTheory.tendsto_measure_iUnion_atTop` in
`Mathlib/MeasureTheory/Measure/Continuity.lean`; `ProbabilityTheory.IsEVar`
in `Statlib/EValues/EVariable.lean`.

### 106.41. Wald's fundamental identity and the operating characteristic

**Statement.** Suppose $P_\theta(Z>0)>0$, $P_\theta(Z<0)>0$, and
$\phi(t)=\mathbb E_\theta e^{tZ}<\infty$ for all real $t$. Then
$\mathbb E_\theta[e^{tS_N}\phi(t)^{-N}]=1$ for every real $t$ with
$\phi(t)\ge1$. If $\mathbb E_\theta Z\ne0$, there is exactly one real
$h\ne0$ with $\phi(h)=1$, and $\mathbb E_\theta e^{hS_N}=1$ and
$\mathbb E_\theta N=\mathbb E_\theta S_N/\mathbb E_\theta Z$. If
$S_N\in\{\log A,\log B\}$ almost surely, then
$$L(\theta)=\frac{B^h-1}{B^h-A^h},\qquad
\mathbb E_\theta N=\frac{L(\theta)\log A+(1-L(\theta))\log B}
{\mathbb E_\theta Z}.$$
Mathlib has moment-generating functions and their multiplicativity over
independent sums, and Statlib proves Wald's identity
$\mathbb ES_N=\mathbb EN\,\mathbb EZ$ for integrable stopping times of
independent identically distributed sequences. Optional stopping of the
exponential martingale at the unbounded time $N$, the fundamental identity,
the existence of $h$, and the operating characteristic are missing from all
three libraries.

**Argument.** As in 106.37, $P_\theta(N>km)\le(1-p^m)^k$, so $N$ has
geometric tails and $\mathbb E_\theta N<\infty$. Fix $t$ with $\phi(t)\ge1$
and put $M_n=e^{tS_n}\phi(t)^{-n}$. Independence and multiplicativity of
moment-generating functions make $(M_n)$ a positive martingale with
$M_0=1$, so optional stopping at the bounded times $N\wedge n$ gives
$\mathbb EM_{N\wedge n}=1$. Split
$M_{N\wedge n}=M_N1_{\{N\le n\}}+M_n1_{\{N>n\}}$. On $\{N>n\}$,
$S_n\in(\log A,\log B)$ and $\phi(t)^{-n}\le1$, so the second term is at
most $C\,1_{\{N>n\}}$ with $C=e^{|t|\max(|\log A|,|\log B|)}$, and its
expectation tends to $0$. The first term increases to $M_N$, so monotone
convergence gives $\mathbb EM_N=1$.

The function $\phi$ is finite, continuous and strictly convex (the law of
$Z$ is not a point mass), with $\phi(0)=1$, $\phi'(0)=\mathbb E_\theta Z$,
and $\phi(t)\to\infty$ as $t\to\pm\infty$ because $Z$ takes both signs with
positive probability. If $\mathbb E_\theta Z>0$, then $\phi<1$ just left of
$0$ and the intermediate value theorem gives a root $h<0$; symmetrically for
$\mathbb E_\theta Z<0$; strict convexity allows at most two roots of
$\phi=1$. Then $\phi(h)=1$ gives $\mathbb E_\theta e^{hS_N}=1$, and
$\mathbb E_\theta N=\mathbb E_\theta S_N/\mathbb E_\theta Z$ is Wald's
identity, from Statlib as in 106.37 (it uses only
$\mathbb E_\theta N<\infty$ and $\mathbb E_\theta|Z|<\infty$). If $S_N\in\{\log A,\log B\}$ almost surely,
with $L=P_\theta(S_N=\log A)$ the identity reads $LA^h+(1-L)B^h=1$, which
solves to the stated $L(\theta)$ because $A^h\ne B^h$; and
$\mathbb E_\theta S_N=L\log A+(1-L)\log B$.

**Library results.** `ProbabilityTheory.iIndepFun.mgf_sum` in
`Mathlib/Probability/Moments/Basic.lean`;
`ProbabilityTheory.continuous_mgf` and `ProbabilityTheory.deriv_mgf_zero` in
`Mathlib/Probability/Moments/MGFAnalytic.lean`;
`MeasureTheory.condExp_indep_eq` in
`Mathlib/Probability/ConditionalExpectation.lean`;
`MeasureTheory.Submartingale.expected_stoppedValue_mono` in
`Mathlib/Probability/Martingale/OptionalStopping.lean`;
`MeasureTheory.lintegral_iSup` (monotone convergence) in
`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`; the results listed for
106.37.

### 106.42. Anscombe's theorem

**Statement.** Let $X_1,X_2,\ldots$ be independent and identically
distributed with mean $\mu$ and variance $\sigma^2\in(0,\infty)$, and let
$N_a$ be positive integer random variables with $N_a/a\to_Pk\in(0,\infty)$.
Then $(S_{N_a}-N_a\mu)/(\sigma\sqrt{N_a})\Rightarrow N(0,1)$, with no
independence required between $N_a$ and the observations. More generally, if
$Y_n\Rightarrow Y$ and $(Y_n)$ is uniformly continuous in probability, then
$Y_{N_a}\Rightarrow Y$. Random-index limit theorems are absent from all three
libraries; TauCeti's strong law and central limit theorem for the renewal
count are the nearest results.

**Argument.** *General statement.* Put $n_a=\lceil ka\rceil\to\infty$, so
$N_a/n_a\to_P1$. Given $\varepsilon>0$, take $\delta$ from the uniform
continuity condition and $\delta'>0$ with $(1+\delta')/(1-\delta')\le
1+\delta$; let $m_a=\lceil(1-\delta')n_a\rceil$. On the event
$\{|N_a-n_a|\le\delta'n_a\}$, whose probability tends to $1$, both $N_a$ and
$n_a$ lie in $[m_a,m_a+\delta m_a]$, so
$$
\mathbb P(|Y_{N_a}-Y_{n_a}|>2\varepsilon)\le
\mathbb P\Bigl(\max_{0\le j\le\delta m_a}|Y_{m_a+j}-Y_{m_a}|>\varepsilon\Bigr)
+o(1)\le\varepsilon+o(1).
$$
Thus $Y_{N_a}-Y_{n_a}\to_P0$. Since $n_a\to\infty$, $Y_{n_a}\Rightarrow Y$,
and convergence in distribution is preserved under perturbations tending to
$0$ in probability.

*Sums.* Let $Y_n=(S_n-n\mu)/(\sigma\sqrt n)$; the central limit theorem gives
$Y_n\Rightarrow N(0,1)$. For uniform continuity in probability, write
$$
Y_{n+j}-Y_n=\frac{S'_{n+j}-S'_n}{\sigma\sqrt{n+j}}
+Y_n\Bigl(\sqrt{\tfrac n{n+j}}-1\Bigr)
$$
with $S'$ the centred sums. For the first term, Kolmogorov's maximal
inequality gives
$\mathbb P(\max_{j\le\delta n}|S'_{n+j}-S'_n|\ge\varepsilon\sigma\sqrt n)
\le\delta/\varepsilon^2$; for the second, $|Y_n|$ is bounded in probability
and the factor is at most $1-(1+\delta)^{-1/2}$ in absolute value; both are
small for small $\delta$, uniformly in $n$. Kolmogorov's inequality is
elementary: with $\tau$ the first $j$ at which the partial sum reaches
level $\lambda$, $\mathbb E[S_j'(S'_m-S'_j)1_{\{\tau=j\}}]=0$ by
independence, so $\mathbb ES_m'^2\ge\sum_j\mathbb E[S_j'^21_{\{\tau=j\}}]
\ge\lambda^2\mathbb P(\max_jS_j'^2\ge\lambda^2)$. Since
$(S_{N_a}-N_a\mu)/(\sigma\sqrt{N_a})$ is exactly $Y_{N_a}$, the general
statement gives the conclusion; no independence between $N_a$ and the
observations is used.

**Library results.** `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`
in `Mathlib/Probability/CentralLimitTheorem.lean`;
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`;
`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` in
`Mathlib/Probability/Independence/Integration.lean`;
`ProbabilityTheory.variance_sum` in `Mathlib/Probability/Moments/Variance.lean`.
The limit along $n_a\to\infty$ is the composition of the central limit
theorem with a tendsto map of the index.

### 106.44. Optimality of CUSUM

**Statement.** For every $A>0$, $\mathbb E_\infty T_{\mathrm{CS}}(A)\ge A$, and
the worst-case delay of the CUSUM procedure equals
$\mathbb E_0T_{\mathrm{CS}}(A)$. If $\gamma>1$ and $A_\gamma$ is chosen so
that $\mathbb E_\infty T_{\mathrm{CS}}(A_\gamma)=\gamma$, then CUSUM minimizes
Lorden's worst-case delay over $\mathcal C_\gamma$ (Moustakides), and the
first-order asymptotics $\log\gamma/I$ hold (Lorden). Optimal-stopping theory
and change-detection procedures are absent from all three libraries; Statlib's
divergences of laws stopped at a stopping time are ingredients of lower
bounds on the delay.

**Scope.** The argument gives the first sentence. Moustakides' optimality and
Lorden's asymptotics remain a gap.

**Argument.** The CUSUM statistic satisfies Page's recursion
$V_n=L_n\max(1,V_{n-1})$ with $V_0=0$, as one sees by splitting the maximum
over $k<n$ at $k=n-1$. Put $T=T_{\mathrm{CS}}(A)$.

*False-alarm bound.* Let $R_n=\sum_{k=0}^{n-1}\prod_{i=k+1}^nL_i$ (the
Shiryaev–Roberts statistic), so $R_n\ge V_n$ and $R_n=L_n(1+R_{n-1})$. Under
$P_\infty$, $L_n$ is independent of the past with
$\mathbb E_\infty L_n=P_1(f_0>0)\le1$, so $R_n-n$ is a supermartingale with
$R_0=0$. Optional stopping at $T\wedge n$ gives
$\mathbb E_\infty R_{T\wedge n}\le\mathbb E_\infty(T\wedge n)$. On
$\{T\le n\}$, $R_{T\wedge n}\ge V_T\ge A$, and $R\ge0$, so
$A\,P_\infty(T\le n)\le\mathbb E_\infty(T\wedge n)$. Letting $n\to\infty$
gives $\mathbb E_\infty T\ge A\,P_\infty(T<\infty)$, and if
$P_\infty(T=\infty)>0$ then $\mathbb E_\infty T=\infty$.

*Worst-case delay.* For $w\ge1$ define $W^w_1=wL_{\nu+1}$ and
$W^w_j=L_{\nu+j}\max(1,W^w_{j-1})$, and let $T^w$ be the first $j$ with
$W^w_j\ge A$. By induction $W^w_j$ is nondecreasing in $w$, so $T^w$ is
nonincreasing in $w$. On $\{T>\nu\}$ the post-change CUSUM path is
$W^{\max(1,V_\nu)}$, so $T-\nu=T^{\max(1,V_\nu)}$. Under $P_\nu$ the
post-change observations are independent of $X_1,\ldots,X_\nu$ with density
$f_1$, so
$\mathbb E_\nu[(T-\nu)^+\mid X_1,\ldots,X_\nu]
=1_{\{T>\nu\}}\,g(\max(1,V_\nu))$ with $g(w)=\mathbb E_0T^w\le g(1)$, and
$g(1)=\mathbb E_0T$. Hence the essential supremum is at most $\mathbb E_0T$
for every $\nu$, and for $\nu=0$ the conditional expectation is
$\mathbb E_0T$ itself; the worst-case delay equals $\mathbb E_0T$.

**Library results.** `MeasureTheory.Submartingale.expected_stoppedValue_mono`
in `Mathlib/Probability/Martingale/OptionalStopping.lean`;
`MeasureTheory.Supermartingale.neg` in
`Mathlib/Probability/Martingale/Basic.lean`; `MeasureTheory.hittingBtwn` in
`Mathlib/Probability/Process/HittingTime.lean`;
`MeasureTheory.condExp_indep_eq` in
`Mathlib/Probability/ConditionalExpectation.lean`;
`ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib` in
`Mathlib/Probability/Kernel/CondDistrib.lean` (conditioning on the
pre-change block of a product space).

### 106.48. Extremal index

**Statement.** The sequence has extremal index $\theta\in(0,1]$ when, for
every $\tau>0$, $P(M_n\le u_n)\to e^{-\theta\tau}$ for every $(u_n)$ with
$n(1-F(u_n))\to\tau$. An independent sequence has extremal index $1$; more
generally, if $D(u_n)$ and $D'(u_n)$ hold for every such sequence and every
$\tau>0$, the extremal index is $1$ (Leadbetter). Absent from all three
libraries.

**Scope.** The argument gives the independent case. Leadbetter's theorem
under $D(u_n)$ and $D'(u_n)$ remains a gap.

**Argument.** A strictly stationary independent sequence is independent and
identically distributed. By TauCeti's law of the maximum,
$P(M_n\le u_n)=F(u_n)^n$, and the forward direction of 106.50 gives
$F(u_n)^n\to e^{-\tau}$ whenever $n(1-F(u_n))\to\tau$. So $\theta=1$.

**Library results.** As for 106.50.

### 106.50. Poisson approximation for exceedances

**Statement.** For independent observations, $0\le\tau\le\infty$, and real
$u_n$, $P(M_n\le u_n)\to e^{-\tau}$ if and only if $n(1-F(u_n))\to\tau$; for
finite $\tau$ the number of exceedances of $u_n$ then converges in law to a
Poisson law of mean $\tau$. For $0<\tau<\infty$, levels with
$n(1-F(u_n))\to\tau$ exist if and only if both
$\lim_{x\uparrow x_F}F(x)=1$ and $(1-F(x))/(1-F(x-))\to1$ as
$x\uparrow x_F$; hence the Poisson and geometric laws are in no domain of
attraction. The forward direction for finite $\tau$ follows by a short
argument from TauCeti's formula $P(M_n\le u)=F(u)^n$, Mathlib's limit
$(1+a_n)^n\to e^t$ when $na_n\to t$, and Mathlib's binomial-to-Poisson limit
theorem; it is not assembled. The converse, the case $\tau=\infty$, and the
existence criterion for the levels are missing.

**Scope.** The argument gives the first sentence in full (both directions,
$0\le\tau\le\infty$) and the Poisson limit of the number of exceedances. The
endpoint and tail-ratio conditions for the existence of these levels, and
their consequence for the Poisson and geometric laws, are outside this
argument.

**Argument.** The observations are independent with common distribution
function $F$, so $P(M_n\le u_n)=F_n^n$ with $F_n=F(u_n)$; put
$p_n=1-F_n$.

*Forward, $\tau<\infty$.* $np_n\to\tau$ gives $(1-p_n)^n\to e^{-\tau}$ by
Mathlib's limit. *Forward, $\tau=\infty$.* From $\log x\le x-1$,
$F_n^n\le e^{-np_n}\to0$.

*Converse.* Two elementary bounds suffice: for $x\in(0,1]$,
$1-x\le-\log x\le(1-x)/x$. Suppose $F_n^n\to e^{-\tau}$ with $\tau<\infty$.
Then $F_n>0$ eventually and $-n\log F_n\to\tau$, so $\log F_n\to0$,
$F_n\to1$, and the bounds give
$np_n\le-n\log F_n\le np_n/F_n$, whence $np_n\to\tau$. Suppose $F_n^n\to0$
but $np_n\not\to\infty$; along a subsequence $np_n\le C$, so $p_n\to0$, and
$F_n^n\ge e^{-np_n/F_n}\ge e^{-2C}$ eventually along it, a contradiction.

*Exceedances.* The indicators $1_{\{X_i>u_n\}}$, $i\le n$, are independent
Bernoulli variables with parameter $p_n$, so the number of exceedances $K_n$
has $P(K_n=j)=\binom njp_n^j(1-p_n)^{n-j}$, by counting subsets and
independence. Mathlib's binomial-to-Poisson theorem gives pointwise
convergence to the Poisson probabilities $q_j=e^{-\tau}\tau^j/j!$. Since both
sides sum to $1$, Scheffé's argument (dominated convergence of
$(q_j-P(K_n=j))^+\le q_j$, Tannery's theorem) gives
$\sum_j|P(K_n=j)-q_j|\to0$, hence convergence in law.

**Library results.** `TauCeti.Probability.cdf_max_iid` in
`TauCeti/Probability/Distributions/Relations.lean`;
`Real.tendsto_one_add_pow_exp_of_tendsto` in
`Mathlib/Analysis/SpecialFunctions/Complex/LogBounds.lean`;
`ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop` in
`Mathlib/Probability/Distributions/Poisson/PoissonLimitThm.lean`;
`ProbabilityTheory.poissonMeasure` in
`Mathlib/Probability/Distributions/Poisson/Basic.lean`;
`Real.log_le_sub_one_of_pos` and `Real.one_sub_inv_le_log_of_pos` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`;
`tendsto_tsum_of_dominated_convergence` in
`Mathlib/Analysis/Normed/Group/Tannery.lean`.

## 107. Statistical learning and machine learning

### 107.2. Rademacher bound

**Statement.** For a countable class $\mathcal F$ of measurable functions
with values in $[0,1]$, or any such class for which the suprema below are
measurable,
$\mathbb E\sup_{f}(P_n-P)f\le2\,\mathop{\mathrm{Rad}}_n(\mathcal F)$, and
likewise with $P-P_n$. With probability at least $1-\delta$,
$$\sup_{f\in\mathcal F}|(P_n-P)f|
\le2\mathop{\mathrm{Rad}}_n(\mathcal F)+\sqrt{\frac{\log(2/\delta)}{2n}},$$
and, with probability at least $1-\delta$,
$\sup_f(P-P_n)f\le2\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
+3\sqrt{\log(2/\delta)/(2n)}$. TauCeti supplies the Rademacher law and
McDiarmid's inequality for finite products, which give the high-probability
steps; missing are the complexity itself and the symmetrization inequality
(CKMA 07.33).

**Argument.** The complexities are new definitions. Take $\mathcal F$
nonempty; by the hypothesis the suprema below are measurable, and all of
them are bounded, hence integrable.

*Symmetrization.* Let $Z'_1,\ldots,Z'_n$ be an independent copy of the sample
and $P'_n$ its empirical measure. Since $Pf=\mathbb E'P'_nf$,
$$\sup_f(P_n-P)f=\sup_f\mathbb E'(P_n-P'_n)f
\le\mathbb E'\sup_f(P_n-P'_n)f .$$
Take expectations and use Fubini. For independent Rademacher signs
$\sigma_i$, the vectors $(f(Z_i)-f(Z'_i))_{i,f}$ and
$(\sigma_i(f(Z_i)-f(Z'_i)))_{i,f}$ have the same joint law: swapping $Z_i$
and $Z'_i$ for the indices with $\sigma_i=-1$ preserves the product law.
Hence
$$\mathbb E\sup_f(P_n-P)f
\le\mathbb E\sup_f\frac1n\sum_i\sigma_i(f(Z_i)-f(Z'_i))
\le\mathbb E\sup_f\frac1n\sum_i\sigma_if(Z_i)
+\mathbb E\sup_f\frac1n\sum_i(-\sigma_i)f(Z'_i)
=2\mathop{\mathrm{Rad}}_n(\mathcal F),$$
since $-\sigma$ has the law of $\sigma$. The same computation with $P-P_n$
gives the second expectation bound.

*Concentration.* The maps $\Phi_+(z)=\sup_f(P_n-P)f$,
$\Phi_-(z)=\sup_f(P-P_n)f$ and $z\mapsto\widehat{\mathop{\mathrm{Rad}}}_n$
change by at most $1/n$ when one coordinate of the sample is changed,
because $f$ takes values in $[0,1]$. McDiarmid's inequality gives each of
them, centered, a sub-Gaussian moment-generating function with variance
proxy $n(1/(2n))^2=1/(4n)$, so for $t\ge0$
$$\mathbb P(\Phi-\mathbb E\Phi\ge t)\le e^{-2nt^2},$$
and the same for $\mathbb E\Phi-\Phi$. With
$t=\sqrt{\log(2/\delta)/(2n)}$ each tail is $\delta/2$. Since
$\sup_f|(P_n-P)f|=\max(\Phi_+,\Phi_-)$, a union bound over the upper tails
of $\Phi_+$ and $\Phi_-$ gives the first high-probability bound. For the
second, combine the upper tail of $\Phi_-$ with the lower tail of
$\widehat{\mathop{\mathrm{Rad}}}_n$,
$\mathop{\mathrm{Rad}}_n\le\widehat{\mathop{\mathrm{Rad}}}_n+t$, each at
level $\delta/2$; this gives
$\Phi_-\le2\widehat{\mathop{\mathrm{Rad}}}_n+3t$, with a constant $3$.

**Library results.** `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`
and `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences_fin` in
`TauCeti/Probability/McDiarmid.lean`;
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` in
`Mathlib/Probability/Moments/SubGaussian.lean`;
`TauCeti.Probability.rademacherMeasure` in
`TauCeti/Probability/Distributions/Rademacher/Basic.lean`;
`ProbabilityTheory.exists_iid` in `Mathlib/Probability/HasLawExists.lean`;
`MeasureTheory.measure_iUnion_fintype_le` in
`Mathlib/MeasureTheory/OuterMeasure/Basic.lean`; Fubini for product
measures.

### 107.5. Hedge

**Statement.** For $K$ actions and loss vectors $\ell_t\in[0,1]^K$, possibly
chosen adaptively, the exponentially weighted forecaster with weights
$p_t(i)\propto\exp(-\eta\sum_{s<t}\ell_s(i))$ and $\eta=\sqrt{8(\log K)/T}$
has regret at most $\sqrt{(T/2)\log K}$ after $T$ rounds against the best
fixed action. The argument is short from Mathlib: bound the logarithm of the
ratio of successive normalizing sums by Hoeffding's lemma applied to $p_t$,
and compare the telescoped sum with the weight of the best action. No library
defines the forecaster or regret.

**Argument.** The forecaster and the regret
$\sum_{t\le T}\langle p_t,\ell_t\rangle-\min_i\sum_{t\le T}\ell_t(i)$ are new
definitions. The bound is deterministic, for every sequence of losses, so
adaptivity costs nothing. If $K=1$ the regret is $0$; let $K\ge2$, so
$\eta>0$, and $T\ge1$.

Put $L_t(i)=\sum_{s\le t}\ell_s(i)$ and $W_t=\sum_ie^{-\eta L_{t-1}(i)}$, so
$W_1=K$ and $p_t(i)=e^{-\eta L_{t-1}(i)}/W_t$. Then
$$\log\frac{W_{t+1}}{W_t}=\log\sum_ip_t(i)e^{-\eta\ell_t(i)}
\le-\eta\langle p_t,\ell_t\rangle+\frac{\eta^2}8 .$$
This is Hoeffding's lemma for the variable $i\mapsto\ell_t(i)\in[0,1]$
under the probability $p_t$ on the $K$ actions. Summing over $t$ and using
$W_{T+1}\ge e^{-\eta L_T(i)}$ for every $i$,
$$-\eta L_T(i)-\log K\le\log\frac{W_{T+1}}{W_1}
\le-\eta\sum_t\langle p_t,\ell_t\rangle+\frac{T\eta^2}8 .$$
Hence the regret is at most $\log K/\eta+\eta T/8$, which equals
$2\sqrt{T\log K/8}=\sqrt{(T/2)\log K}$ for the stated $\eta$.

**Library results.** `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` and
the field `ProbabilityTheory.HasSubgaussianMGF.mgf_le` in
`Mathlib/Probability/Moments/SubGaussian.lean`, applied to the finite
measure $\sum_ip_t(i)\delta_i$; `Real.log_le_log` and the exponential laws in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`.

### 107.6. Split conformal prediction

**Statement.** Let $S_1,\ldots,S_n$ be calibration scores and $S_{n+1}$ the
test score, computed by a score depending only on an independent training
part and on the pair at which it is evaluated, and suppose the $n+1$
calibration and test pairs are exchangeable conditionally on the training
part. For $\alpha\in(0,1)$ put $k=\lceil(n+1)(1-\alpha)\rceil$, let $S_{(k)}$
be the $k$th smallest calibration score ($+\infty$ if $k>n$), and let
$C(x)=\{y:s(x,y)\le S_{(k)}\}$. Then
$\mathbb P(Y_{n+1}\in C(X_{n+1}))\ge1-\alpha$, and the probability is at
most $1-\alpha+1/(n+1)$ if the $n+1$ scores are almost surely distinct.
TauCeti defines exchangeability of sequences; the statement follows from the
uniform distribution of the rank of $S_{n+1}$ among $n+1$ exchangeable
scores, which none of the three libraries states.

**Argument.** Conditionally on the training part the score function is
fixed, so the vector $(S_1,\ldots,S_{n+1})$ is exchangeable under the
conditional law. It suffices to prove the bounds for an exchangeable vector
and integrate over the training part. Note $1\le k\le n+1$, and
$Y_{n+1}\in C(X_{n+1})$ exactly when $S_{n+1}\le S_{(k)}$.

If $k=n+1$, the event is sure, and $k>n$ means $\alpha<1/(n+1)$, so
$1\le1-\alpha+1/(n+1)$. Let $k\le n$. For $i\le n+1$ let $A_i$ be the event
that $S_i$ is at most the $k$th smallest of the other $n$ scores; then
$\{S_{n+1}\le S_{(k)}\}=A_{n+1}$. The transposition of $i$ and $n+1$
preserves the law, so $\mathbb P(A_i)=\mathbb P(A_{n+1})$ for all $i$.
Deterministically, at least $k$ of the events occur. Sort the values as
$v_{(1)}\le\cdots\le v_{(n+1)}$ and take an index $i$ placed at a position
$j\le k$. Removing it leaves $v_{(k+1)}\ge S_i$ as the $k$th smallest of
the others. If the values are distinct, exactly $k$ occur: an index at a
position $j>k$ leaves $v_{(k)}<S_i$. Hence
$$(n+1)\mathbb P(A_{n+1})=\mathbb E\sum_i1_{A_i}\ge k\ge(n+1)(1-\alpha),$$
with equality $=k<(n+1)(1-\alpha)+1$ in the distinct case.

**Library results.** `TauCeti.Probability.ExchangeableAt` and
`TauCeti.Probability.Exchangeable` in
`TauCeti/Probability/Exchangeability/Basic.lean`, for the invariance of the
law of the first $n+1$ coordinates under `Equiv.Perm (Fin (n+1))`;
`ProbabilityTheory.condDistrib` in
`Mathlib/Probability/Kernel/CondDistrib.lean` for conditioning on the
training part. The counting step is finite combinatorics.

### 107.7. No free lunch

**Statement.** On an infinite feature space, for every $n$, every
classification rule based on $n$ observations, and every $\varepsilon>0$,
some distribution with Bayes error zero gives the rule expected $0$–$1$
error at least $1/2-\varepsilon$.

**Argument.** The argument uses labels in $\{0,1\}$ and a measurable rule
$g_n(x;(x_1,y_1),\ldots,(x_n,y_n))$; an independent randomization of the
rule changes nothing below. Choose $K\ge n/(2\varepsilon)$ distinct points
$a_1,\ldots,a_K$, which exist because the space is infinite. For a labelling
$b\in\{0,1\}^K$ let $P_b$ be the law of $(X,b(X))$ with $X$ uniform on the
$a_j$. The label is a function of $X$, so the Bayes error is zero.

Average the expected error of the rule over the $2^K$ labellings. It is a
finite sum over $b$, $X$ and $X_1,\ldots,X_n$. On the terms with
$X\notin\{X_1,\ldots,X_n\}$, flipping $b$ at $X$ is an involution of the
labellings. It changes neither the sample nor the prediction
$g_n(X;\ldots)$, and it changes the label $b(X)$. Exactly one of each pair
of terms is an error, so
$$2^{-K}\sum_b\mathbb E_{P_b}\bigl[1\{g_n(X)\ne Y\}\bigr]
\ge\frac12\,\mathbb P\bigl(X\notin\{X_1,\ldots,X_n\}\bigr)
=\frac12\Bigl(1-\frac1K\Bigr)^n\ge\frac12-\frac n{2K}
\ge\frac12-\varepsilon,$$
by Bernoulli's inequality. Some $b$ attains at least the average.

**Library results.** `Infinite.natEmbedding` in
`Mathlib/Data/Fintype/EquivFin.lean`; `one_add_mul_le_pow` in
`Mathlib/Algebra/Order/Ring/Pow.lean`; finite sums of Dirac masses with
`MeasureTheory.lintegral_dirac'` in
`Mathlib/MeasureTheory/Integral/Lebesgue/Countable.lean`.

### 107.8. Bayes classification risk

**Statement.** For binary labels, the classifier $g^*=1_{\{\eta\ge1/2\}}$
minimizes risk, and for every measurable $g$,
$$R(g)-R(g^*)=\mathbb E\bigl[|2\eta(X)-1|1_{\{g(X)\ne g^*(X)\}}\bigr].$$
A plug-in rule $\hat g=1_{\{\hat\eta\ge1/2\}}$ built from independent
training data has conditional excess risk at most
$2\mathbb E|\hat\eta(X)-\eta(X)|$; if $P(|\eta(X)-1/2|\le t)\le Ct^\alpha$ for
all $t>0$ and $\|\hat\eta-\eta\|_\infty\le\delta$, it is at most
$2C\delta^{\alpha+1}$. Statlib proves the first assertion in likelihood-ratio
form: with the conditional laws of $X$ given $Y=0$ and $Y=1$ and the law of
$Y$ as prior, its Bayes test between the two laws is the rule
$1_{\{\eta\ge1/2\}}$, it is a Bayes rule for the $0$–$1$ loss, and its Bayes
risk is $\mathbb E\min(\eta(X),1-\eta(X))$. The excess-risk identity for an
arbitrary classifier, the plug-in bound, and the margin bound are not stated;
the identity follows by writing
$R(g)=\mathbb E[\eta(X)1_{\{g=0\}}+(1-\eta(X))1_{\{g=1\}}]$ and comparing
pointwise. The item is the common base of 107.11 and 107.14.

**Argument.** Let $\pi$ be the law of $Y$ on $\{0,1\}$ and $\mu,\nu$ the
conditional laws of $X$ given $Y=0$ and $Y=1$, so that the joint law of
$(Y,X)$ is $\pi\otimes\kappa$ for the kernel $\kappa$ sending $0$ to $\mu$
and $1$ to $\nu$, and the law $P_X$ of $X$ is $\kappa\circ\pi$. The posterior
weights of the two labels are $\pi\{1\}\,d\nu/dP_X$ and
$\pi\{0\}\,d\mu/dP_X$ almost everywhere, so these are $\eta$ and $1-\eta$.
Statlib's test answers $1$ exactly where
$\pi\{0\}\,d\mu/dP_X\le\pi\{1\}\,d\nu/dP_X$, that is, where $\eta\ge1/2$; so
it is $g^*$ up to a $P_X$-null set. It is an argmin, hence Bayes, estimator
for the $0$–$1$ loss among all randomized rules, which is the minimality of
$g^*$.

For a measurable classifier $g=1_E$, Statlib's risk formula for a
deterministic test gives
$$R(g)=\pi\{0\}\mu(E)+\pi\{1\}\nu(E^c)
=\mathbb E\bigl[(1-\eta(X))1_{\{g(X)=1\}}+\eta(X)1_{\{g(X)=0\}}\bigr].$$
Pointwise, the integrand for $g$ minus that for $g^*$ vanishes where
$g=g^*$, and equals $|2\eta-1|$ where they differ: if $\eta\ge1/2$ and
$g=0$ it is $\eta-(1-\eta)$, and symmetrically. This gives the identity.

For the plug-in rule, condition on the training data, which is independent
of $(X,Y)$; then $\hat\eta$ and $\hat g$ are fixed measurable functions, and
the identity applies to $\hat g$. Where $\hat g\ne g^*$, the numbers
$\eta-1/2$ and $\hat\eta-1/2$ lie on different sides of $0$ or one is $0$,
so $|\eta-1/2|\le|\hat\eta-\eta|$. Hence
$|2\eta-1|1_{\{\hat g\ne g^*\}}\le2|\hat\eta-\eta|$, which gives the first
bound. Under $\|\hat\eta-\eta\|_\infty\le\delta$ the same inclusion gives
$\{\hat g\ne g^*\}\subseteq\{|\eta-1/2|\le\delta\}$, so the excess risk is
at most $2\delta\,P(|\eta(X)-1/2|\le\delta)\le2C\delta^{\alpha+1}$.

**Library results.** `ProbabilityTheory.binaryArgminEstimator`,
`ProbabilityTheory.isArgminEstimator_binaryArgminEstimator`,
`ProbabilityTheory.avgRisk_binary_of_deterministic_indicator` and
`ProbabilityTheory.bayesBinaryRisk_eq_lintegral_min` in
`Statlib/Testing/Binary.lean`;
`ProbabilityTheory.posterior_boolKernel_apply_true` and
`ProbabilityTheory.posterior_boolKernel_apply_false` in
`Mathlib/Probability/Kernel/Posterior.lean`;
`ProbabilityTheory.IsArgminEstimator.isBayesEstimator` in
`Mathlib/Probability/Decision/BayesEstimator.lean`;
`ProbabilityTheory.Kernel.boolKernel` in
`Mathlib/Probability/Kernel/Basic.lean`; `ProbabilityTheory.condDistrib` and
`ProbabilityTheory.compProd_map_condDistrib` in
`Mathlib/Probability/Kernel/CondDistrib.lean`; independence and Fubini in
`Mathlib/Probability/Independence/Basic.lean` and
`Mathlib/MeasureTheory/Measure/Prod.lean`.

### 107.10. Margin bound

**Statement.** For a class $\mathcal H$ of real functions and $\rho>0$, with
probability at least $1-\delta$ every $h\in\mathcal H$ satisfies
$$R(h)\le\hat R_{n,\rho}(h)+\frac2\rho\mathop{\mathrm{Rad}}_n(\mathcal H)
+\sqrt{\frac{\log(1/\delta)}{2n}},$$
and the same holds with $\widehat{\mathop{\mathrm{Rad}}}_n$ in place of
$\mathop{\mathrm{Rad}}_n$ and $3\sqrt{\log(2/\delta)/(2n)}$ as last term.
For a kernel ball $\|h\|_{\mathcal H}\le\Lambda$ with $K(x,x)\le r^2$ the
complexity term is at most $2\Lambda r/(\rho\sqrt n)$. Beyond the
ingredients of 107.2, the contraction (Talagrand) lemma for Rademacher
averages is missing.

**Scope.** Only the kernel-ball estimate
$\widehat{\mathop{\mathrm{Rad}}}_n\le\Lambda r/\sqrt n$, and hence
$\mathop{\mathrm{Rad}}_n\le\Lambda r/\sqrt n$, is proved here. The margin
bound itself needs the contraction lemma and remains a gap.

**Argument.** Let $k_x$ be the kernel function at $x$, so
$h(x)=\langle h,k_x\rangle$ and $\langle k_x,k_y\rangle=K(x,y)$. By
Cauchy–Schwarz, with equality attained,
$$\sup_{\|h\|\le\Lambda}\sum_i\sigma_ih(x_i)
=\Lambda\Bigl\|\sum_i\sigma_ik_{x_i}\Bigr\| .$$
By Jensen's inequality for the square root, and because
$\mathbb E\sigma_i\sigma_j=\delta_{ij}$,
$$\mathbb E_\sigma\Bigl\|\sum_i\sigma_ik_{x_i}\Bigr\|
\le\Bigl(\sum_{i,j}\mathbb E\sigma_i\sigma_jK(x_i,x_j)\Bigr)^{1/2}
=\Bigl(\sum_iK(x_i,x_i)\Bigr)^{1/2}\le r\sqrt n .$$
Divide by $n$. The bound holds for every sample, so it passes to
$\mathop{\mathrm{Rad}}_n$.

**Library results.** `RKHS`, `RKHS.kerFun_inner`, `RKHS.kernel_inner` and
`RKHS.norm_apply_le` in `Mathlib/Analysis/InnerProductSpace/Reproducing.lean`
(scalar case $V=\mathbb R$); `ConvexOn.map_integral_le` in
`Mathlib/Analysis/Convex/Integral.lean`; `TauCeti.Probability.rademacherMeasure`
in `TauCeti/Probability/Distributions/Rademacher/Basic.lean`.

### 107.11. Comparison inequality for convex surrogates

**Statement.** Let $\Phi:\mathbb R\to[0,\infty)$ be convex and
nondecreasing, differentiable at $0$ with $\Phi'(0)>0$, let
$R_\Phi(h)=\mathbb E\Phi(-Yh(X))$ with infimum $R_\Phi^*$, and
$L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$. Every minimizer of
$u\mapsto L_\Phi(x,u)$ over $[-\infty,\infty]$ has the sign of
$\eta(x)-1/2$ when this is nonzero, and $u=0$ is a minimizer when
$\eta(x)=1/2$. If $|\eta(x)-\frac12|^s\le c^s(L_\Phi(x,0)-\inf_uL_\Phi(x,u))$
for all $x$, with $s\ge1$ and $c>0$, then $R(h)-R^*\le2c(R_\Phi(h)-R_\Phi^*)^{1/s}$
for every measurable $h$ with $P(h(X)=0)=0$, a condition that cannot be
dropped since $R(h)=P(Yh(X)\le0)$ counts $h(X)=0$ as an error; the hinge
loss admits $s=1$, $c=1/2$ and the squared hinge $s=2$, $c=1/2$.

**Argument.** For $\eta\equiv1/2$ and $h\equiv0$ one has $R(h)-R^*=1/2$,
while $R_\Phi(h)=\Phi(0)=R_\Phi^*$ by convexity; this is why the condition
$P(h(X)=0)=0$ is needed. The argument below also proves the inequality for
every measurable $h$ when $R(h)$ is the error of $\mathop{\mathrm{sign}}h$
with any fixed value of $\mathop{\mathrm{sign}}0\in\{-1,1\}$.

Write $L(u)=L_\Phi(x,u)$, a finite convex function of $u$
with $L'(0)=\Phi'(0)(1-2\eta(x))$, extended to $\pm\infty$ by its monotone
limits. If $\eta(x)>1/2$ then $L'(0)<0$, so $0$ is not a minimizer, and for
$u<0$, $L(u)\ge L(0)+uL'(0)>L(0)$, which tends to $+\infty$ as
$u\to-\infty$; so every minimizer is positive. The case $\eta(x)<1/2$ is
symmetric. If $\eta(x)=1/2$, $L(u)=(\Phi(u)+\Phi(-u))/2\ge\Phi(0)$.

Let $L^*(x)=\inf_uL_\Phi(x,u)$. It is the infimum over rational $u$, by
continuity of $\Phi$, so it is measurable. Choosing for each $x$ the first
rational in an enumeration that is within $1/m$ of the infimum gives
measurable $h_m$ with $R_\Phi(h_m)\le\mathbb EL^*(X)+1/m$. Hence
$R_\Phi^*=\mathbb EL^*(X)$; it is finite since $L^*\le\Phi(0)$.

By 107.8, under $P(h(X)=0)=0$ or the sign convention,
$R(h)-R^*=\mathbb E[|2\eta-1|1_W]$, where $W$ is the set on which the
classification by $h$ disagrees with $g^*$. Removing from $W$ the set
$\{\eta=1/2\}$, where the weight vanishes, leaves a subset of
$\{h(X)(2\eta(X)-1)\le0\}$.
On $W$ convexity gives $L(h(x))\ge L(0)+h(x)L'(0)\ge L(0)$. Therefore, by
Jensen's inequality for $t\mapsto t^s$,
$$R(h)-R^*=2\mathbb E\bigl[|\eta-\tfrac12|1_W\bigr]
\le2\bigl(\mathbb E[|\eta-\tfrac12|^s1_W]\bigr)^{1/s}
\le2c\bigl(\mathbb E[(L(0)-L^*)1_W]\bigr)^{1/s}
\le2c\bigl(R_\Phi(h)-R_\Phi^*\bigr)^{1/s}.$$
The last step uses $L(0)\le L(h(x))$ on $W$ and $L(h(x))-L^*\ge0$ off $W$.
If $R_\Phi(h)=\infty$ there is nothing to prove.

For the hinge loss, $L(0)=1$ and $L^*=1-|2\eta-1|$, attained at $u=\pm1$,
so $L(0)-L^*=2|\eta-\frac12|$. For the squared hinge, $L(0)=1$ and the
minimum over $[-1,1]$ is $1-(2\eta-1)^2$ at $u=2\eta-1$; outside $[-1,1]$
the value is larger. So $L(0)-L^*=4|\eta-\frac12|^2$. Both give $c=1/2$.

**Library results.** `ConvexOn` slope inequalities in
`Mathlib/Analysis/Convex/Slope.lean` and `Mathlib/Analysis/Convex/Deriv.lean`;
`ConvexOn.map_integral_le` in `Mathlib/Analysis/Convex/Integral.lean`;
`ProbabilityTheory.condDistrib` in
`Mathlib/Probability/Kernel/CondDistrib.lean`; measurable infima over
countable families in `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`.

### 107.12. Generalization of stable algorithms

**Statement.** If the algorithm is uniformly $\beta$-stable,
$(S,z)\mapsto L(h_S,z)$ is measurable, and $0\le L(h_S,z)\le M$, then with probability at least $1-\delta$,
$$R(h_S)\le R_n(h_S)+\beta+(2n\beta+M)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
Regularized empirical risk minimization
$h_S\in\mathop{\mathrm{argmin}}_h(R_n(h)+\lambda\|h\|_{\mathcal H}^2)$ over
a reproducing-kernel Hilbert space with $K(x,x)\le r^2$ and a loss convex
and $G$-Lipschitz in the prediction is uniformly stable with
$\beta\le G^2r^2/(n\lambda)$. The first bound follows from TauCeti's
McDiarmid inequality applied to $R(h_S)-R_n(h_S)$, whose expectation is at
most $\beta$ and whose bounded differences are at most $2\beta+M/n$; missing
are the notion of an algorithm on samples, this argument, and the stability
of regularized kernel minimization.

**Argument.** An algorithm is a new definition, a map $S\mapsto h_S$ with
$(S,z)\mapsto L(h_S,z)$ measurable, as the statement assumes.
Put $\Phi(S)=R(h_S)-R_n(h_S)$.

*Expectation.* Let $z'$ be an independent copy of one point and $S^i$ the
sample with $z_i$ replaced by $z'$. Exchanging $z_i$ and $z'$ preserves the
product law, so $\mathbb EL(h_S,z_i)=\mathbb EL(h_{S^i},z')$, and
$$\mathbb E\Phi=\frac1n\sum_i\mathbb E\bigl[L(h_S,z')-L(h_{S^i},z')\bigr]
\le\beta .$$

*Bounded differences.* If $S,S'$ differ in coordinate $i$, then
$|R(h_S)-R(h_{S'})|\le\beta$. In $R_n$ the $n-1$ common terms change by at
most $\beta/n$ each and the replaced term by at most $M/n$. So $\Phi$
changes by at most $c=2\beta+M/n$. McDiarmid gives variance proxy
$nc^2/4$ and the tail $\mathbb P(\Phi-\mathbb E\Phi\ge t)\le
e^{-2t^2/(nc^2)}$. At level $\delta$,
$t=c\sqrt{n\log(1/\delta)/2}=(2n\beta+M)\sqrt{\log(1/\delta)/(2n)}$.

*Stability of regularized minimization.* Let $F_S(h)=R_n(h)+\lambda\|h\|^2$
with minimizer $h=h_S$, and $h'=h_{S'}$. Since $R_n$ is convex in $h$, the
minimality of $h$ along the segment to $h'$ gives
$R_n(h')-R_n(h)+2\lambda\langle h,h'-h\rangle\ge0$, hence
$F_S(h')-F_S(h)\ge\lambda\|h'-h\|^2$; likewise
$F_{S'}(h)-F_{S'}(h')\ge\lambda\|h-h'\|^2$. Adding, the regularizers
cancel and
$$2\lambda\|h-h'\|^2\le\frac1n\bigl[(L(h',z_i)-L(h,z_i))
+(L(h,z'_i)-L(h',z'_i))\bigr]\le\frac{2Gr}n\|h-h'\|,$$
because $|g(x)|\le r\|g\|$ by the reproducing property. Thus
$\|h-h'\|\le Gr/(n\lambda)$ and
$|L(h,z)-L(h',z)|\le Gr\|h-h'\|\le G^2r^2/(n\lambda)$. Existence of the
minimizers is assumed in the statement, and the stability bound needs no
measurability.

**Library results.** `TauCeti.Probability.hasSubgaussianMGF_of_bounded_differences`
in `TauCeti/Probability/McDiarmid.lean`;
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` in
`Mathlib/Probability/Moments/SubGaussian.lean`; `RKHS.norm_apply_le` in
`Mathlib/Analysis/InnerProductSpace/Reproducing.lean`; product measures
`MeasureTheory.Measure.pi` and their invariance under permutation of
coordinates, `MeasureTheory.measurePreserving_piCongrLeft`, in
`Mathlib/MeasureTheory/Constructions/Pi.lean`.

### 107.24. AdaBoost: training error and margins

**Statement.** On a sample $(x_i,y_i)$, $i\le m$, with labels and base
classifiers in $\{-1,1\}$, AdaBoost starts from uniform weights $D_1$,
chooses $h_t$ with weighted error $\varepsilon_t$, sets
$\alpha_t=\frac12\log((1-\varepsilon_t)/\varepsilon_t)$ and
$D_{t+1}(i)\propto D_t(i)e^{-\alpha_ty_ih_t(x_i)}$, and returns
$f=\sum_{t\le T}\alpha_th_t$. If $0<\varepsilon_t<1/2$ for all $t$, the
training error of $\mathop{\mathrm{sign}}f$ is at most
$$\prod_{t=1}^T2\sqrt{\varepsilon_t(1-\varepsilon_t)}
\le\exp\Bigl(-2\sum_{t=1}^T(\tfrac12-\varepsilon_t)^2\Bigr),$$
and the fraction of points with normalized margin
$y_if(x_i)/\|\alpha\|_1\le\rho$ is at most
$2^T\prod_t\sqrt{\varepsilon_t^{1-\rho}(1-\varepsilon_t)^{1+\rho}}$. The
empirical Rademacher complexity of the convex hull of a class equals that of
the class, so the margin bound 107.10 applies to $f/\|\alpha\|_1$ without
dependence on $T$.

**Scope.** The two training bounds and the equality of empirical Rademacher
complexities of a class and its convex hull are proved here. The final
consequence relies on the margin bound 107.10, which remains a gap.

**Argument.** Let $Z_t=\sum_iD_t(i)e^{-\alpha_ty_ih_t(x_i)}$ be the
normalizer. Splitting by correct and incorrect points,
$Z_t=(1-\varepsilon_t)e^{-\alpha_t}+\varepsilon_te^{\alpha_t}
=2\sqrt{\varepsilon_t(1-\varepsilon_t)}$. Unrolling the recursion,
$D_{T+1}(i)=e^{-y_if(x_i)}/(m\prod_tZ_t)$, and these weights sum to one. As
$1\{y_if(x_i)\le0\}\le e^{-y_if(x_i)}$, whatever the value of
$\mathop{\mathrm{sign}}0$, the training error is at most
$m^{-1}\sum_ie^{-y_if(x_i)}=\prod_tZ_t$. With $\gamma_t=\frac12-\varepsilon_t$,
$Z_t=\sqrt{1-4\gamma_t^2}\le\sqrt{e^{-4\gamma_t^2}}=e^{-2\gamma_t^2}$.

All $\alpha_t>0$, so $\|\alpha\|_1=\sum_t\alpha_t$, and
$1\{y_if(x_i)\le\rho\|\alpha\|_1\}\le\exp(\rho\sum_t\alpha_t-y_if(x_i))$.
The fraction is therefore at most
$\prod_te^{\rho\alpha_t}Z_t$, and
$e^{\rho\alpha_t}=((1-\varepsilon_t)/\varepsilon_t)^{\rho/2}$ gives the
factor $2\varepsilon_t^{(1-\rho)/2}(1-\varepsilon_t)^{(1+\rho)/2}$.

For the complexity, a member of the convex hull is a finite combination
$\sum_j\lambda_jh_j$. For fixed signs,
$\sum_i\sigma_i\sum_j\lambda_jh_j(x_i)\le\max_j\sum_i\sigma_ih_j(x_i)$, so
the suprema over the class and over its hull agree; take expectations over
$\sigma$. Since $f/\|\alpha\|_1$ lies in the convex hull of the base class,
107.10 would apply to it.

**Library results.** `Real.add_one_le_exp` in
`Mathlib/Analysis/Complex/Exponential.lean`; `Real.sqrt_le_sqrt` in
`Mathlib/Analysis/Real/Sqrt.lean`; the logarithm and exponential laws in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`; `convexHull` in
`Mathlib/Analysis/Convex/Hull.lean` with `Finset.centerMass` combinations
from `Mathlib/Analysis/Convex/Combination.lean`.

### 107.26. Variational representation of the cumulant function

**Statement.** $\nabla A$ maps $\Omega$ onto $\mathcal M^\circ$; for
$\mu\in\mathcal M^\circ$, $A^*(\mu)$ is the negative entropy of the unique
member with mean $\mu$, and $A^*=+\infty$ off $\bar{\mathcal M}$. Moreover
$A(\theta)=\sup_{\mu\in\mathcal M}\{\langle\theta,\mu\rangle-A^*(\mu)\}$,
attained uniquely at $\mu=\mathbb E_\theta\phi$. For a finite discrete model
$\max_x\langle\theta,\phi(x)\rangle
=\max_{\mu\in\bar{\mathcal M}}\langle\theta,\mu\rangle
=\lim_{\beta\to\infty}A(\beta\theta)/\beta$. Mathlib proves the
one-parameter case of the gradient identity: the first two derivatives of
the cumulant-generating function are the tilted mean and variance;
multiparameter families, $\mathcal M$, and the duality are missing.

**Scope.** Only the final assertion, for a finite discrete model, is proved
here. The mean-parameter duality remains a gap.

**Argument.** Let the state space $\mathcal X$ be finite and let $\nu$ give
each point positive mass. If $\nu$ has null points, they are removed and the
maximum over $x$ is taken over the support. Then
$A(\theta)=\log\sum_x\nu(x)e^{\langle\theta,\phi(x)\rangle}$ and
$\mathcal M=\{\sum_xq(x)\phi(x)\}$ over probability vectors $q$ for which
$q/\nu$ is a density, that is, over all probability vectors. So $\mathcal M$
is the convex hull of the finitely many points $\phi(x)$, a compact set, and
$\bar{\mathcal M}=\mathcal M$. A linear functional attains its maximum over
a convex hull at a generating point, which gives the first equality. Write
$a=\max_x\langle\theta,\phi(x)\rangle$, $\nu_{\min}=\min_x\nu(x)$ and
$|\nu|=\sum_x\nu(x)$. For $\beta>0$, keeping one maximizing term or bounding
every term by the largest gives
$$a+\frac{\log\nu_{\min}}\beta\le\frac{A(\beta\theta)}\beta
\le a+\frac{\log|\nu|}\beta,$$
and both bounds tend to $a$.

**Library results.** `ConvexOn.exists_ge_of_mem_convexHull` in
`Mathlib/Analysis/Convex/Jensen.lean`, applied to the linear functional;
`Finset.centerMass_mem_convexHull` in
`Mathlib/Analysis/Convex/Combination.lean`; `Finset.single_le_sum` and
`Finset.sum_le_card_nsmul`; `Real.log_le_log` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`.

### 107.31. Ridgeless least squares

**Statement.** For independent standard normal $x_i\in\mathbb R^p$,
$y_i=x_i^\top\beta+\varepsilon_i$ with independent centered errors of
variance $\sigma^2$, and $\hat\beta$ the minimum-norm least-squares
estimator, the expected excess prediction risk
$\mathbb E(x^\top\hat\beta-x^\top\beta)^2$ is $\sigma^2p/(n-p-1)$ for
$n>p+1$ and $\|\beta\|^2(1-n/p)+\sigma^2n/(p-n-1)$ for $p>n+1$; if
$p/n\to\gamma\ne1$ and $\|\beta\|^2\to r^2$, the limits are
$\sigma^2\gamma/(1-\gamma)$ and $r^2(1-1/\gamma)+\sigma^2/(\gamma-1)$.
TauCeti proves the Wishart law of a Gaussian Gram matrix and the
inverse-Wishart mean $(n-p-1)^{-1}S$, which give the case $n>p+1$ by a short
computation; the case $p>n+1$ needs the corresponding moments of the
projection onto the row space, and neither the risk identities nor the
limits are stated.

**Scope.** The case $n>p+1$ and its limit $\gamma<1$ are proved here. The
overparameterized case remains a gap.

**Argument.** The errors are taken independent of the design, and the test
point $x\sim N(0,I_p)$ independent of the training data. Then
$\mathbb E(x^\top v)^2=\mathbb E\|v\|^2$ for $v=\hat\beta-\beta$. Let $X$
be the $n\times p$ design. Since $n\ge p$, the Gram matrix $X^\top X$ has the
nonsingular Wishart law $W_p(n,I)$, which is almost surely positive
definite. Then $\hat\beta$ is the ordinary least-squares estimator and
$v=(X^\top X)^{-1}X^\top\varepsilon$. Conditioning on $X$,
$$\mathbb E[\|v\|^2\mid X]=\sigma^2\mathop{\mathrm{tr}}
\bigl((X^\top X)^{-1}X^\top X(X^\top X)^{-1}\bigr)
=\sigma^2\mathop{\mathrm{tr}}(X^\top X)^{-1}.$$
By definition the inverse-Wishart law $IW(n,I)$ is the image of $W_p(n,I)$
under inversion, with mean $I/(n-p-1)$ for $n>p+1$. So
$\mathbb E\|v\|^2=\sigma^2p/(n-p-1)$. If $p/n\to\gamma<1$ then
$p/(n-p-1)=(p/n)/(1-p/n-1/n)\to\gamma/(1-\gamma)$.

**Library results.** `TauCeti.Probability.hasLaw_wishartGram_gaussian_nonsingularWishartMeasure`
and `TauCeti.Probability.ae_posDef_wishartGramMeasure` in
`TauCeti/Probability/Distributions/Wishart/Agreement.lean`;
`TauCeti.Probability.inverseWishartMeasure_def` in
`TauCeti/Probability/Distributions/Wishart/Inverse/Basic.lean`;
`TauCeti.Probability.integral_id_inverseWishartMeasure` in
`TauCeti/Probability/Distributions/Wishart/Inverse/Moments.lean`;
`ProbabilityTheory.multivariateGaussian` in
`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`.

### 107.40. Implicit bias of gradient descent

**Statement.** For $\frac12\|X\theta-y\|^2$, gradient descent with constant
step $0<\eta<2/\lambda_{\max}(X^\top X)$ from $\theta_0$ converges to
$X^+y+(I-X^+X)\theta_0$, the minimum-norm solution when $\theta_0=0$. For
linearly separable data and the logistic loss there is $\eta_0>0$ such that
gradient descent with any step in $(0,\eta_0)$ from any start has
$\|\theta_t\|\to\infty$ and $\theta_t/\|\theta_t\|\to\hat\theta/\|\hat\theta\|$,
with $\hat\theta$ the hard-margin solution (Soudry et al.). TauCeti
constructs the Moore–Penrose inverse of a linear map between
finite-dimensional inner product spaces from its singular system and
characterizes it by the four Penrose equations, which supplies the limit
$X^+y+(I-X^+X)\theta_0$; no library proves a convergence theorem for
gradient descent, and the logistic implicit bias is absent.

**Scope.** The least-squares assertion is proved here. The logistic
assertion remains a gap.

**Argument.** Let $A=X^\top X$, symmetric and positive semidefinite, and let
$R=\mathop{\mathrm{range}}A$, so that $\ker A=\ker X=R^\perp$ and
$R=\mathop{\mathrm{range}}X^\top$. Take $X^+$ to be TauCeti's Moore–Penrose
inverse of the Euclidean map of $X$; a matrix satisfying the Penrose
equations gives the same relation for the associated maps. By the Penrose
equations $XX^+$ and $X^+X$ are symmetric idempotents, hence orthogonal
projections. From $XX^+X=X$, the kernel of $X^+X$ is $\ker X$, so $X^+X$ is
the orthogonal projection onto $R$; likewise $XX^+$ projects onto
$\mathop{\mathrm{range}}X$. Then $X^+y=X^+XX^+y\in R$, and
$AX^+y=X^\top(XX^+y)=X^\top y$ because $y-XX^+y$ is orthogonal to the range
of $X$, which $X^\top$ annihilates. So $X^+y$ is the element of $R$ solving
the normal equations, unique because $A$ is injective on $R$, and it is the
minimum-norm least-squares solution. Since $X(I-X^+X)=0$,
$\theta^*=X^+y+(I-X^+X)\theta_0$ also solves the normal equations.

The iteration is $\theta_{t+1}=\theta_t-\eta(A\theta_t-X^\top y)$, so
$e_t=\theta_t-\theta^*$ satisfies $e_{t+1}=(I-\eta A)e_t$. Further
$e_0=X^+X\theta_0-X^+y\in R$, and $R$ is invariant under $A$. Restricted to
$R$, the operator $I-\eta A$ is symmetric with eigenvalues $1-\eta\lambda$,
$\lambda\in(0,\lambda_{\max}]$, all of absolute value less than one. Its
norm $q$ is therefore below one, and $\|e_t\|\le q^t\|e_0\|\to0$. If $X=0$
then $\theta_t=\theta_0=\theta^*$ and the step condition is vacuous.

**Library results.** `LinearMap.moorePenroseInverse`,
`LinearMap.IsMoorePenroseInverse`,
`LinearMap.isMoorePenroseInverse_moorePenroseInverse` and
`Matrix.isMoorePenroseInverse_toEuclideanLin_of_penrose` in
`TauCeti/Analysis/InnerProductSpace/MoorePenrose.lean`;
`LinearMap.IsSymmetric.eigenvectorBasis` and
`LinearMap.IsSymmetric.apply_eigenvectorBasis` in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`;
`Submodule.starProjection` and `Submodule.starProjection_norm_le` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`;
`exists_norm_eq_iInf_of_complete_convex` in
`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` for the
minimum-norm characterization; `tendsto_pow_atTop_nhds_zero_of_lt_one` in
`Mathlib/Analysis/SpecificLimits/Basic.lean`.

### 107.52. Adversarial bandits

**Statement.** Against an oblivious sequence of loss vectors in $[0,1]^K$,
$K\ge2$, Exp3 with the importance-weighted estimates
$\hat\ell_t(i)=\ell_t(i)1_{\{I_t=i\}}/p_t(i)$, which are conditionally
unbiased, and $\eta=\sqrt{2\log K/(TK)}$ has expected regret at most
$\sqrt{2TK\log K}$ after $T$ rounds.

**Argument.** The algorithm is a new definition. With the losses fixed in
advance, the law of $(I_1,\ldots,I_T)$ is a finite distribution on
$\{1,\ldots,K\}^T$. It is the product of the conditional laws $p_t$, each a
function of $I_1,\ldots,I_{t-1}$, and can be built directly or by
Ionescu–Tulcea. Here
$p_t(i)\propto\exp(-\eta\sum_{s<t}\hat\ell_s(i))$ is positive, so the
estimates are defined.

Pathwise, as in 107.5 but with the nonnegative unbounded estimates, put
$W_t=\sum_ie^{-\eta\hat L_{t-1}(i)}$. The elementary inequalities
$e^{-u}\le1-u+u^2/2$ for $u\ge0$ and $\log(1+v)\le v$ give
$$\log\frac{W_{t+1}}{W_t}\le-\eta\langle p_t,\hat\ell_t\rangle
+\frac{\eta^2}2\sum_ip_t(i)\hat\ell_t(i)^2 .$$
Telescoping and $W_{T+1}\ge e^{-\eta\hat L_T(i)}$ yield, for every $i$,
$$\sum_t\langle p_t,\hat\ell_t\rangle-\hat L_T(i)\le\frac{\log K}\eta
+\frac\eta2\sum_t\sum_jp_t(j)\hat\ell_t(j)^2 .$$
Given the past, $\mathbb E\hat\ell_t(j)=\ell_t(j)$, so
$\mathbb E\langle p_t,\hat\ell_t\rangle=\mathbb E\ell_t(I_t)$ and
$\mathbb E\hat L_T(i)=L_T(i)$. Also
$\mathbb E\sum_jp_t(j)\hat\ell_t(j)^2=\mathbb E\sum_j\ell_t(j)^2\le K$.
Taking expectations, the expected regret against every fixed $i$ is at most
$\log K/\eta+\eta TK/2=\sqrt{2TK\log K}$.

**Library results.** `Real.add_one_le_exp` in
`Mathlib/Analysis/Complex/Exponential.lean` (its consequence
$e^{-u}\ge1-u$ is the derivative bound behind $e^{-u}\le1-u+u^2/2$, via
`monotoneOn_of_deriv_nonneg` in `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`);
`Real.log_le_sub_one_of_pos` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`;
`ProbabilityTheory.Kernel.traj` in
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean` for the law of the
interaction, and conditional expectation in
`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`.

### 107.59. Sample complexity with a generative model

**Statement.** In a finite discounted model with known rewards
$r(s,a)\in[0,1]$, draw for each state-action pair $N$ independent next states
from $P(\cdot\mid s,a)$, let $\hat P$ be the empirical transition law, and
let hats denote quantities of the model with $\hat P$ in place of $P$. For
every stationary policy $\pi$,
$Q^\pi-\hat Q^\pi=\gamma(I-\gamma\hat P^\pi)^{-1}(P-\hat P)V^\pi$, with
$\hat P^\pi$ the empirical state-action transition matrix under $\pi$; hence
$\|Q^\pi-\hat Q^\pi\|_\infty\le\gamma(1-\gamma)^{-1}\|(P-\hat P)V^\pi\|_\infty$.
There is an absolute constant $c$ such that, if $\varepsilon\le1$,
$\delta\in(0,1)$, and
$N\ge c\log(c|S||A|/\delta)/((1-\gamma)^3\varepsilon^2)$, then with
probability at least $1-\delta$, $\|\hat Q^\star-Q^\star\|_\infty\le\varepsilon$.
If $\varepsilon\le(1-\gamma)^{-1/2}$, the same condition on $N$ makes an
optimal policy $\hat\pi$ of the empirical model satisfy
$\|Q^{\hat\pi}-Q^\star\|_\infty\le\varepsilon$ with probability at least
$1-\delta$. Conversely, there are absolute constants
$\varepsilon_0,\delta_0\in(0,1)$ and $c'>0$ and a class of models such that,
for $\varepsilon<\varepsilon_0$ and $\delta<\delta_0$, every procedure that
on each model of the class outputs $\hat Q$ with
$\|\hat Q-Q^\star\|_\infty\le\varepsilon$ with probability at least
$1-\delta$ uses at least $c'|S||A|\log(c'/\delta)/((1-\gamma)^3\varepsilon^2)$
samples from the generative model. The identity is one step from Mathlib's
Neumann series. The $(1-\gamma)^{-3}$ rate needs a Bernstein-type variance
argument: TauCeti's Bernstein inequality for independent bounded summands
gives the concentration of $(\hat P-P)V$ for each fixed $V$, but the bound
on the total variance of the discounted returns and the passage to the
data-dependent values $\hat V^\star$ are missing, and so is the lower bound.

**Scope.** The identity and the sup-norm bound for a fixed stationary policy
are proved here. The rates and the lower bound remain gaps.

**Argument.** The model is a new definition. View $P$ as the
$(S\times A)\times S$ matrix of transition probabilities and $\Pi^\pi$ as the
$S\times(S\times A)$ matrix of $\pi$, so $V=\Pi^\pi Q$ and $P^\pi=P\Pi^\pi$.
Both are row-stochastic. In the $\ell^\infty$ operator norm $\|\gamma
P^\pi\|=\gamma<1$, so $I-\gamma P^\pi$ is invertible with Neumann series.
Define $Q^\pi=(I-\gamma P^\pi)^{-1}r$, the unique solution of
$Q^\pi=r+\gamma PV^\pi$, and likewise $\hat Q^\pi$ with $\hat P$; since
$N\ge1$, $\hat P$ is row-stochastic too. Subtracting,
$$Q^\pi-\hat Q^\pi=\gamma(P-\hat P)V^\pi+\gamma\hat P\Pi^\pi(Q^\pi-\hat Q^\pi),$$
so $(I-\gamma\hat P^\pi)(Q^\pi-\hat Q^\pi)=\gamma(P-\hat P)V^\pi$, the
identity. The Neumann series bounds the inverse by
$\sum_k\gamma^k=(1-\gamma)^{-1}$ in the $\ell^\infty$ operator norm, giving
the bound.

**Library results.** `NormedRing.inverse_one_sub` in
`Mathlib/Analysis/Normed/Ring/Units.lean`; `tsum_geometric_of_norm_lt_one`
and `tsum_geometric_le_of_norm_lt_one` in
`Mathlib/Analysis/SpecificLimits/Normed.lean`; `Matrix.linftyOpNormedRing`
and `Matrix.linfty_opNorm_def` in `Mathlib/Analysis/Matrix/Normed.lean`.

### 107.60. Temporal differences with linear features

**Statement.** For a fixed policy, let the states form an irreducible
aperiodic chain on $\{1,\ldots,n\}$ with transition matrix $P$, stationary
law $\varpi$, one-step costs $g(i,j)$, and value $V$, and let $\Phi$ be an
$n\times K$ feature matrix of full column rank with rows $\phi(i)^\top$. For
$\lambda\in[0,1]$, TD($\lambda$) runs along one trajectory $(i_t)$ with
$d_t=g(i_t,i_{t+1})+\gamma\phi(i_{t+1})^\top r_t-\phi(i_t)^\top r_t$,
$z_t=\sum_{k\le t}(\gamma\lambda)^{t-k}\phi(i_k)$, and
$r_{t+1}=r_t+\alpha_td_tz_t$. Let $\Pi$ be the orthogonal projection onto
the range of $\Phi$ in the $\varpi$-weighted norm. If the steps are positive
and deterministic with $\sum_t\alpha_t=\infty$ and
$\sum_t\alpha_t^2<\infty$, then $r_t\to r^\star$ almost surely, where
$\Phi r^\star$ is the unique fixed point of $\Pi T^{(\lambda)}$, with
$T^{(\lambda)}=(1-\lambda)\sum_{m\ge0}\lambda^mT^{m+1}$ for $\lambda<1$,
$T^{(1)}$ the constant map to $V$, and $T$ the policy Bellman operator.
Moreover
$$\|\Phi r^\star-V\|_\varpi\le\frac{1-\gamma\lambda}{1-\gamma}
\|\Pi V-V\|_\varpi,$$
and for $\lambda=1$ the limit is $\Pi V$.

**Scope.** Existence and uniqueness of the fixed point $\Phi r^\star$, the
error bound, and its identification for $\lambda=1$ are proved here. The
almost-sure convergence of TD($\lambda$) needs a stochastic-approximation
theorem and remains a gap.

**Argument.** Irreducibility makes $\varpi$ positive. If $\varpi(j)=0$, then
$0=\sum_i\varpi(i)P(i,j)$ forces $\varpi(i)=0$ whenever $P(i,j)>0$, and this
propagates to every state. So $\langle u,v\rangle_\varpi=\sum_i\varpi(i)u_iv_i$
is an inner product on $\mathbb R^n$, and $\Pi$ is its orthogonal
projection, of norm at most one. Jensen's inequality and stationarity give
$\|Pv\|_\varpi^2=\sum_i\varpi(i)(\sum_jP(i,j)v_j)^2
\le\sum_j\varpi(j)v_j^2$.

Let $Tv=\bar g+\gamma Pv$, so $T^{m+1}v-T^{m+1}w=\gamma^{m+1}P^{m+1}(v-w)$,
and for $\lambda<1$
$$\|T^{(\lambda)}v-T^{(\lambda)}w\|_\varpi\le(1-\lambda)\sum_m\lambda^m
\gamma^{m+1}\|v-w\|_\varpi=\kappa\|v-w\|_\varpi,\qquad
\kappa=\frac{\gamma(1-\lambda)}{1-\gamma\lambda}<1 .$$
For $\lambda=1$ the map is constant, with $\kappa=0$. Hence $\Pi T^{(\lambda)}$
is a contraction of the range of $\Phi$, a complete space, and it has a
unique fixed point $\Phi r^\star$. The vector $r^\star$ is unique because
$\Phi$ has full column rank. Since $TV=V$, also $T^{(\lambda)}V=V$, and
$$\|\Phi r^\star-V\|_\varpi\le\|\Pi T^{(\lambda)}\Phi r^\star-\Pi T^{(\lambda)}V\|_\varpi
+\|\Pi V-V\|_\varpi\le\kappa\|\Phi r^\star-V\|_\varpi+\|\Pi V-V\|_\varpi .$$
Rearranging gives the bound, as $1/(1-\kappa)=(1-\gamma\lambda)/(1-\gamma)$.
For $\lambda=1$ the fixed point is $\Pi V$.

**Library results.** `ContractingWith.fixedPoint_isFixedPt` and
`ContractingWith.fixedPoint_unique` in
`Mathlib/Topology/MetricSpace/Contracting.lean`; `Submodule.starProjection`
and `Submodule.starProjection_norm_le` in
`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`, for the weighted
inner product; `ConvexOn.map_sum_le` in `Mathlib/Analysis/Convex/Jensen.lean`;
`tsum_geometric_of_lt_one` in `Mathlib/Analysis/SpecificLimits/Basic.lean`.

### 107.65. Composition

**Statement.** The adaptive composition of $k$ mechanisms that are
$(\varepsilon_i,\delta_i)$-differentially private is
$(\sum\varepsilon_i,\sum\delta_i)$-differentially private. If each is
$(\varepsilon,\delta)$-private, then for every $\delta'\in(0,1)$ the
composition is $(\varepsilon',k\delta+\delta')$-private with
$\varepsilon'=\sqrt{2k\log(1/\delta')}\,\varepsilon+k\varepsilon(e^\varepsilon-1)$.
The advanced bound would use the Azuma–Hoeffding inequality, which Mathlib
has in conditional sub-Gaussian form and TauCeti for bounded martingale
differences; no privacy notion is defined.

**Scope.** The basic adaptive composition bound is proved here. The advanced
composition bound remains a gap.

**Argument.** Differential privacy is a new definition. A mechanism is a
Markov kernel from data sets to outputs, and adaptive composition is the
composition product: the $i$th mechanism is a kernel from (data set, earlier
outputs) that is $(\varepsilon_i,\delta_i)$-private for each fixed earlier
output. By induction it suffices to treat two mechanisms: $\mu_D$ for the
first, and $\kappa_{D,y}$ for the second with first output $y$.

First, privacy extends from sets to functions $f$ with values in $[0,1]$. By
the layer-cake formula $\int f\,d\mu_D=\int_0^1\mu_D(f>t)\,dt$, so
$\int f\,d\mu_D\le e^{\varepsilon_1}\int f\,d\mu_{D'}+\delta_1$. For a
measurable set $C$ of output pairs, with sections $C_y$, put
$g(y)=\kappa_{D',y}(C_y)$ and $f=\min(1,e^{\varepsilon_2}g)$. Using
$\min(1,u+\delta)\le\min(1,u)+\delta$,
$$(\mu_D\otimes\kappa_D)(C)=\int\kappa_{D,y}(C_y)\,d\mu_D
\le\int f\,d\mu_D+\delta_2
\le e^{\varepsilon_1}\int f\,d\mu_{D'}+\delta_1+\delta_2 .$$
Finally $\int f\,d\mu_{D'}\le e^{\varepsilon_2}\int g\,d\mu_{D'}
=e^{\varepsilon_2}(\mu_{D'}\otimes\kappa_{D'})(C)$. Measurability of $g$
and $f$ follows from the kernel property of the composition product.

**Library results.** `MeasureTheory.Measure.compProd_apply` in
`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` and
`ProbabilityTheory.Kernel.compProd_apply` in
`Mathlib/Probability/Kernel/Composition/CompProd.lean`;
`MeasureTheory.lintegral_eq_lintegral_meas_lt` in
`Mathlib/MeasureTheory/Integral/Layercake.lean`.

### 107.74. Sparse vector technique

**Statement.** For an adaptive stream of queries of sensitivity at most $1$
and a public threshold $T$, AboveThreshold draws
$\hat T=T+\mathop{\mathrm{Lap}}(2/\varepsilon)$ and independent noises
$\nu_i\sim\mathop{\mathrm{Lap}}(4/\varepsilon)$, reports "below" while
$f_i(D)+\nu_i<\hat T$, and halts with "above" at the first exceedance. It is
$\varepsilon$-differentially private whatever the number of queries. If
among the first $k$ queries only the last can satisfy $f_i(D)\ge T-\alpha$,
then with probability at least $1-\beta$ it does not halt before query $k$,
every "above" has $f_i(D)\ge T-\alpha$, and every "below" has
$f_i(D)\le T+\alpha$, where $\alpha=8(\log k+\log(2/\beta))/\varepsilon$.
TauCeti supplies the Laplace law and its distribution function.

**Scope.** The accuracy statement, for the first $k$ queries and
$\beta\in(0,1)$, is proved here. The privacy statement remains a gap.

**Argument.** Before the algorithm halts every report is "below", so the
first $k$ queries $f_1,\ldots,f_k$ are determined by $D$ along the run; they
are fixed functions here. The Laplace law of scale $b$ has two-sided tail
$\mathbb P(|\nu|\ge t)=e^{-t/b}$ for $t\ge0$. Hence each
$\mathbb P(|\nu_i|\ge\alpha/2)=e^{-\alpha\varepsilon/8}=\beta/(2k)$, and
$\mathbb P(|\hat T-T|\ge\alpha/2)=e^{-\alpha\varepsilon/4}
=(\beta/(2k))^2\le\beta/2$. A union bound gives an event $G$ of probability
at least $1-\beta$ on which $|\nu_i|<\alpha/2$ for $i\le k$ and
$|\hat T-T|<\alpha/2$.

On $G$, for $i<k$, $f_i(D)<T-\alpha$ gives $f_i(D)+\nu_i<T-\alpha/2<\hat T$,
so the run does not halt before query $k$. An "above" at $i\le k$ means
$f_i(D)\ge\hat T-\nu_i>T-\alpha$. A "below" means
$f_i(D)<\hat T-\nu_i<T+\alpha$.

**Library results.** `TauCeti.Probability.laplaceMeasure`,
`TauCeti.Probability.measureReal_Ioi_laplaceMeasure`,
`TauCeti.Probability.measureReal_Iic_laplaceMeasure_of_le` and
`TauCeti.Probability.laplaceMeasure_map_add_const` in
`TauCeti/Probability/Distributions/Laplace/Basic.lean`;
`MeasureTheory.measure_iUnion_fintype_le` in
`Mathlib/MeasureTheory/OuterMeasure/Basic.lean`.

### 107.75. Contraction under local privacy

**Statement.** If $Q$ is $\varepsilon$-locally private, then for all input
laws $P_1,P_2$,
$$D(M_{P_1}\|M_{P_2})+D(M_{P_2}\|M_{P_1})
\le4(e^\varepsilon-1)^2\|P_1-P_2\|_{\mathrm{TV}}^2,$$
and for $n$ individuals with independent inputs, released through
$\varepsilon$-locally private kernels that may depend on earlier releases,
the same holds for the joint release laws with an extra factor $n$. The
tensorization step follows from Mathlib's divergence chain rule once the
single-release bound is known; TauCeti's Pinsker inequality bounds total
variation by divergence, the opposite direction. Statlib's data-processing
inequalities for total variation under a Markov kernel and for mutual
information under kernels acting on each component give contraction without
the factor $(e^\varepsilon-1)^2$. The reverse bound under a likelihood-ratio
constraint is missing.

**Argument.** Here $\|P_1-P_2\|_{\mathrm{TV}}=\sup_B|P_1(B)-P_2(B)|$. The
proof gives the constant $2$ in place of $4$. Put
$a=(e^\varepsilon-1)\|P_1-P_2\|_{\mathrm{TV}}$.

*Setwise bound.* Write $P_1-P_2=\nu^+-\nu^-$ (Jordan decomposition), both
parts of mass $\|P_1-P_2\|_{\mathrm{TV}}$. For a measurable $B$, local
privacy gives $\sup_xQ(B\mid x)\le e^\varepsilon\inf_xQ(B\mid x)$, so
$$|M_{P_1}(B)-M_{P_2}(B)|
=\Bigl|\int Q(B\mid x)\,d\nu^+-\int Q(B\mid x)\,d\nu^-\Bigr|
\le\|P_1-P_2\|_{\mathrm{TV}}\bigl(\sup_xQ(B\mid x)-\inf_xQ(B\mid x)\bigr)
\le a\,M_{P_j}(B)$$
for $j=1,2$, because each $M_{P_j}(B)$ is an average of $Q(B\mid x)$.

*From setwise to divergence.* Let $\lambda_1,\lambda_2$ be probabilities
with $|\lambda_1(C)-\lambda_2(C)|\le a\lambda_j(C)$ for all $C$ and
$j=1,2$. Then $\lambda_1\ll\lambda_2$, and $\rho=d\lambda_1/d\lambda_2$
satisfies $|\rho-1|\le a\min(1,\rho)$ almost everywhere. Otherwise
integrating over the set where it fails contradicts the setwise bound. With
$\mathrm{kl}(\rho)=\rho\log\rho-\rho+1\le(\rho-1)\log\rho
\le(\rho-1)^2/\min(1,\rho)$,
$$D(\lambda_1\|\lambda_2)=\int\mathrm{kl}(\rho)\,d\lambda_2
\le\int a^2\min(1,\rho)\,d\lambda_2\le a^2 .$$
By symmetry $D(\lambda_2\|\lambda_1)\le a^2$, and the sum is at most
$2a^2\le4a^2$. Apply this to $\lambda_j=M_{P_j}$.

*Tensorization.* Model the releases recursively. The joint law of the first
$i$ releases is $M^i_j=M^{i-1}_j\otimes\kappa_{j,i}$, where
$\kappa_{j,i}(z)=\int Q_i(\cdot\mid x,z)\,dP_j(x)$; this uses that the $i$th
input is independent of the earlier ones. By the setwise bound, for each $z$,
$\kappa_{1,i}(z)$ and $\kappa_{2,i}(z)$ satisfy the hypothesis with the same
$a$. Integrating over sections then shows that $M^{i-1}_1\otimes\kappa_{1,i}$
and $M^{i-1}_1\otimes\kappa_{2,i}$ do too. The chain rule gives
$$D(M^i_1\|M^i_2)=D(M^{i-1}_1\|M^{i-1}_2)
+D(M^{i-1}_1\otimes\kappa_{1,i}\|M^{i-1}_1\otimes\kappa_{2,i})
\le D(M^{i-1}_1\|M^{i-1}_2)+a^2,$$
so $D(M^n_1\|M^n_2)\le na^2$. The same holds with $1,2$ exchanged, and the
sum is at most $2na^2\le4na^2$.

**Library results.** `InformationTheory.klDiv_eq_lintegral_klFun_of_ac` in
`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`;
`InformationTheory.klDiv_compProd_eq_add` in
`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean`;
`MeasureTheory.Measure.compProd_apply` in
`Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`;
`MeasureTheory.SignedMeasure.toJordanDecomposition` in
`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`;
`Real.log_le_sub_one_of_pos` in
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`; Radon–Nikodym
derivatives in `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`.

## 108. Geometry of data: manifolds, topology, optimal transport, and kernels

### 108.1. Cheeger inequality for the normalized Laplacian

**Statement.** For a finite connected weighted graph with at least two
vertices,
$$\frac{\lambda_1}2\le h(G)\le\sqrt{2\lambda_1},$$
and the sharper lower bound $\lambda_1\ge1-\sqrt{1-h(G)^2}$ holds as well.
Mathlib has only the unweighted Laplacian $D-A$ and the Rayleigh-quotient
characterization of extreme eigenvalues; no library defines the
normalized Laplacian, conductance or Cheeger constant, and the sweep-cut
argument for the upper bound is absent.

**Scope.** Only the easy inequality $\lambda_1\le2h(G)$ is proved here. The
sweep-cut upper bound $h(G)\le\sqrt{2\lambda_1}$ and the sharper bound
$\lambda_1\ge1-\sqrt{1-h(G)^2}$ remain gaps.

**Argument.** The weighted graph, $\mathcal L$, volumes and $h(G)$ are new
definitions. Connectedness with at least two vertices makes all degrees
positive. For $f=D^{1/2}g$,
$$\langle\mathcal Lf,f\rangle=\sum_{\{i,j\}\in E}w_{ij}(g_i-g_j)^2,$$
so $\mathcal L$ is symmetric and positive semidefinite, and
$u_0=D^{1/2}\mathbf 1$ satisfies $\mathcal Lu_0=0$. The Courant–Fischer
theorem, applied to $-\mathcal L$, gives
$\lambda_1\le\max\{R(x):x\in V\setminus\{0\}\}$ for every two-dimensional
subspace $V$, with $R$ the Rayleigh quotient. Take
$V=\mathop{\mathrm{span}}\{u_0,u\}$ with $u\perp u_0$. Then
$\langle\mathcal L(au_0+bu),au_0+bu\rangle=b^2\langle\mathcal Lu,u\rangle$, and
$\langle\mathcal Lu,u\rangle\ge0$, so the maximum over $V$ is $R(u)$.

Let $S$ attain $h(G)$, with $\mathop{\mathrm{vol}}S\le\mathop{\mathrm{vol}}S^c$,
and put $g=1_S/\mathop{\mathrm{vol}}S-1_{S^c}/\mathop{\mathrm{vol}}S^c$ and
$u=D^{1/2}g$. Then $\langle u,u_0\rangle=\sum_id_ig_i=0$, and
$$R(u)=\frac{|\partial S|\,(1/\mathop{\mathrm{vol}}S+1/\mathop{\mathrm{vol}}S^c)^2}
{1/\mathop{\mathrm{vol}}S+1/\mathop{\mathrm{vol}}S^c}
=|\partial S|\Bigl(\frac1{\mathop{\mathrm{vol}}S}+\frac1{\mathop{\mathrm{vol}}S^c}\Bigr)
\le\frac{2|\partial S|}{\mathop{\mathrm{vol}}S}=2h(G).$$

**Library results.** `LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`
in `TauCeti/Analysis/InnerProductSpace/CourantFischer.lean`;
`LinearMap.IsSymmetric.eigenvalues` and
`LinearMap.IsSymmetric.eigenvectorBasis` in
`Mathlib/Analysis/InnerProductSpace/Spectrum.lean`; the unweighted
quadratic-form identity `SimpleGraph.lapMatrix_toLinearMap₂'` in
`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean` as a model.

### 108.8. Classical multidimensional scaling

**Statement.** Let $D^{(2)}$ be a symmetric $n\times n$ matrix with zero
diagonal, put $J=I-11^\top/n$ and $B=-JD^{(2)}J/2$. Then $D^{(2)}$ consists
of squared Euclidean distances between some $n$ points if and only if $B$ is
positive semidefinite. If $B=U\Lambda U^\top\ge0$, the rows of
$U\Lambda^{1/2}$ are centered coordinates realizing these distances, unique
up to a Euclidean isometry, and keeping the $k$ largest positive eigenvalues
gives the best rank-at-most-$k$ positive semidefinite approximation to $B$ in
Frobenius norm. Mathlib proves that Gram matrices are positive semidefinite
and has the spectral theorem; TauCeti proves Eckart–Young in operator norm.
The statement follows by a short argument (double centring identifies $B$
with the Gram matrix of centered points; a positive semidefinite $B$ factors
through its spectral decomposition), but neither the Schoenberg criterion
nor the Frobenius best approximation within positive semidefinite matrices
is stated.

**Argument.** Write $d_{ij}=D^{(2)}_{ij}$, $r_i=n^{-1}\sum_jd_{ij}$ and
$s=n^{-1}\sum_ir_i$. Then
$$B_{ij}=-\tfrac12(d_{ij}-r_i-r_j+s),\qquad B_{ii}+B_{jj}-2B_{ij}=d_{ij},$$
using $d_{ii}=0$. If $d_{ij}=\|x_i-x_j\|^2$, expand
$d_{ij}=\|x_i\|^2+\|x_j\|^2-2\langle x_i,x_j\rangle$. Since $J\mathbf 1=0$,
$B=JGJ$ for the Gram matrix $G$, which is the Gram matrix of the centered
points $x_i-\bar x$. So $B\ge0$. Conversely, if $B=U\Lambda U^\top\ge0$, the
rows $y_i$ of $U\Lambda^{1/2}$ have Gram matrix $B$, so
$\|y_i-y_j\|^2=B_{ii}+B_{jj}-2B_{ij}=d_{ij}$. They are centered because
$\|\sum_iy_i\|^2=\mathbf 1^\top B\mathbf 1=0$. If $y'_i$ is another
configuration with the same distances, centring both gives the same Gram
matrix $B$. Then $\sum_ic_iy_i\mapsto\sum_ic_iy'_i$ is a well-defined linear
isometry between the spans, since both sides have squared norm
$c^\top Bc$. Extended to the whole space and composed with the translations,
it is a Euclidean isometry.

For the approximation, let $B$ be symmetric with eigenvalues
$\lambda_1\ge\cdots\ge\lambda_n$ and let $C=\sum_{i\le k}c_iv_iv_i^\top$ be
positive semidefinite of rank at most $k$, with orthonormal $v_i$ and
$c_1\ge\cdots\ge c_k\ge0$. Put $c_{k+1}=0$. Abel summation and Ky Fan's
inequality for the orthonormal families $v_1,\ldots,v_j$ give
$$\mathop{\mathrm{tr}}(BC)=\sum_{j\le k}(c_j-c_{j+1})\sum_{i\le j}\langle Bv_i,v_i\rangle
\le\sum_{j\le k}(c_j-c_{j+1})\sum_{i\le j}\lambda_i=\sum_{i\le k}c_i\lambda_i .$$
Hence
$$\|B-C\|_F^2=\sum_i\lambda_i^2-2\mathop{\mathrm{tr}}(BC)+\sum_ic_i^2
\ge\sum_{i\le k}(\lambda_i-c_i)^2+\sum_{i>k}\lambda_i^2
\ge\sum_{i\le k}(\lambda_i^-)^2+\sum_{i>k}\lambda_i^2,$$
since $c_i\ge0$. Equality holds for
$C^*=\sum_{i\le k}\lambda_i^+u_iu_i^\top$ with eigenvectors $u_i$ of $B$,
which keeps the $k$ largest positive eigenvalues.

**Library results.** `Matrix.posSemidef_gram` in
`Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`;
`Matrix.IsHermitian.spectral_theorem` in
`Mathlib/Analysis/Matrix/Spectrum.lean`;
`LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues` in
`TauCeti/Analysis/InnerProductSpace/KyFan.lean`; `LinearIsometry.extend` in
`Mathlib/Analysis/InnerProductSpace/PiL2.lean`.

### 108.10. Extrinsic projection mean

**Statement.** Let $X_1,X_2,\ldots$ be independent copies of $X$ with
$j(X)\in L^2$, and put $\mu=\mathbb Ej(X)$. The extrinsic means are the
nearest points of $j(M)$ to $\mu$. If this nearest-point projection $P$ is
single-valued and continuously differentiable near $\mu$, then
$$\sqrt n\Bigl(P\bigl(n^{-1}\textstyle\sum_i j(X_i)\bigr)-P(\mu)\Bigr)
\Rightarrow N(0,DP_\mu\Sigma DP_\mu^\top),\qquad
\Sigma=\mathop{\mathrm{Cov}}(j(X)),$$
and the limit is supported on the tangent space at $P(\mu)$. Mathlib's real
central limit theorem with its Cramér–Wold theorem gives the multivariate
limit of the sample mean; missing are the delta method, the nearest-point
projection onto an embedded manifold, and the statement.

**Scope.** The characterization of extrinsic means and the central limit
theorem are proved here, for any closed set $j(M)\subset\mathbb R^D$ with a
projection $P$ as stated. The last clause, that the limit lies in the
tangent space, needs the submanifold structure of $j(M)$ and remains a gap.

**Argument.** For $m\in M$,
$\mathbb E\|j(X)-j(m)\|^2=\mathbb E\|j(X)-\mu\|^2+\|\mu-j(m)\|^2$, because
the cross term has mean zero. So extrinsic means are the minimizers of
$\|\mu-j(m)\|$.

Put $\bar Z_n=n^{-1}\sum_ij(X_i)$. Cramér–Wold reduces the multivariate
central limit theorem to the real one for each $\langle u,j(X)\rangle$. Two
Gaussian vectors whose projections have the same laws are equal in law, so
$\sqrt n(\bar Z_n-\mu)\Rightarrow N(0,\Sigma)$. By the strong law,
$\bar Z_n\to\mu$ almost surely, so $\bar Z_n$ eventually lies in the
neighbourhood where $P$ is defined. Differentiability at $\mu$ gives
$P(z)-P(\mu)-DP_\mu(z-\mu)=\|z-\mu\|\,\rho(z)$ with $\rho(z)\to0$ as
$z\to\mu$. The remainder
$\sqrt n\|\bar Z_n-\mu\|\rho(\bar Z_n)$ is the product of a tight sequence,
which converges in distribution, and a sequence tending to $0$ almost surely.
It therefore tends to $0$ in probability. Slutsky's lemma, in the form of
convergence in distribution under an asymptotically negligible difference,
reduces the limit to that of $DP_\mu\sqrt n(\bar Z_n-\mu)$. The continuous
mapping theorem for the linear map $DP_\mu$ gives
$N(0,DP_\mu\Sigma DP_\mu^\top)$. Only differentiability of $P$ at $\mu$ is
used.

**Library results.** `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`
in `Mathlib/Probability/CentralLimitTheorem.lean`;
`tendstoInDistribution_iff_tendstoInDistribution_inner` in
`Mathlib/Probability/CramerWold.lean`;
`MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub` and
`MeasureTheory.TendstoInDistribution.continuous_comp` in
`Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean`;
`ProbabilityTheory.strong_law_ae` in `Mathlib/Probability/StrongLaw.lean`;
`MeasureTheory.Measure.ext_of_charFun` in
`Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.lean`.

### 108.21. Čech, Rips, and the nerve

**Statement.** In Euclidean space
$\mathrm{Cech}(r)\subseteq\mathrm{Rips}(r)\subseteq\mathrm{Cech}(\sqrt2\,r)$.
With the Rips parameter redefined as the maximum edge length, in any metric
space $\mathrm{Rips}_r\subseteq\mathrm{Cech}_r\subseteq\mathrm{Rips}_{2r}$.
The nerve of a finite collection of closed convex sets in Euclidean space has
the homotopy type of their union. TauCeti proves that the Čech–singular
total complex of an open cover is quasi-isomorphic to the singular chains,
the homological form of the nerve lemma for open covers with acyclic
intersections; the nerve of a cover as a simplicial complex, the homotopy
nerve theorem for closed convex sets, and the Čech and Rips complexes are
absent.

**Scope.** The first Euclidean inclusion
$\mathrm{Cech}(r)\subseteq\mathrm{Rips}(r)$, valid in any metric space, and
both metric inclusions are proved here. The inclusion into
$\mathrm{Cech}(\sqrt2\,r)$, a Jung-type radius bound, and the nerve theorem
remain gaps.

**Argument.** The two complexes are new definitions, as families of
nonempty subsets of the finite set $S$. A simplex $\sigma$ lies in
$\mathrm{Cech}(r)$ when some point $z$ of the ambient space has
$d(z,s)\le r$ for all $s\in\sigma$. In the diameter-$2r$ convention the
triangle inequality $d(s,t)\le d(s,z)+d(z,t)\le2r$ gives
$\mathrm{Cech}(r)\subseteq\mathrm{Rips}(r)$. With the maximum-edge
convention, $\mathrm{Rips}_r$ consists of the subsets of diameter at most
$r$. The same computation gives $\mathrm{Cech}_r\subseteq\mathrm{Rips}_{2r}$.
If $\sigma$ has diameter at most $r$, any vertex $z\in\sigma$ is a common
point of the balls $\overline B(s,r)$, $s\in\sigma$, so
$\mathrm{Rips}_r\subseteq\mathrm{Cech}_r$.

**Library results.** `dist_triangle` and `Metric.mem_closedBall` in
`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`; `Metric.diam` in
`Mathlib/Topology/MetricSpace/Bounded.lean`. No further library result is
needed.

### 108.23. Central limit theorem for landscapes

**Statement.** Realize a persistence landscape as a random element
$\Lambda$ of $L^p(\mathbb N\times\mathbb R)$, with counting and Lebesgue
measure. For independent copies of $\Lambda$, if $1\le p<\infty$ and
$\mathbb E\|\Lambda\|_p<\infty$, their mean converges almost surely in $L^p$
to $\mathbb E\Lambda$. If $2\le p<\infty$ and $\mathbb E\|\Lambda\|_p^2<\infty$,
the centered mean times $\sqrt n$ converges in distribution to a centered
Gaussian random element of $L^p$ with the covariance of $\Lambda$. Mathlib's
strong law for Banach-space valued variables gives the first statement once
landscapes are defined; landscapes are not defined, and no central limit
theorem in $L^p$, $p\ge2$, is available.

**Scope.** The strong law is proved here, for any independent identically
distributed random elements of $L^p(\mathbb N\times\mathbb R)$, landscapes
or not. The central limit theorem remains a gap.

**Argument.** The product of counting measure on $\mathbb N$ and Lebesgue
measure is $\sigma$-finite on a countably generated $\sigma$-algebra, hence
separable. So $L^p$ with $1\le p<\infty$ is a separable Banach space,
second countable, with its Borel $\sigma$-algebra. The hypothesis
$\mathbb E\|\Lambda\|_p<\infty$, with Borel measurability, is Bochner
integrability. Etemadi's strong law in Banach spaces applies, and needs
only pairwise independence; the limit is the Bochner mean
$\mathbb E\Lambda$.

**Library results.** `ProbabilityTheory.strong_law_ae` in
`Mathlib/Probability/StrongLaw.lean`; the instance
`MeasureTheory.Lp.SecondCountableTopology` in
`Mathlib/MeasureTheory/Measure/SeparableMeasure.lean`, with the
separability instance for s-finite measures on countably generated spaces
in the same file.

### 108.24. Stability of the distance to a measure

**Statement.** For probabilities on $\mathbb R^D$ with finite second moment,
$\|d_{\mu,m}-d_{\nu,m}\|_\infty\le m^{-1/2}W_2(\mu,\nu)$. TauCeti has $W_2$;
the distance to a measure and its stability are absent.

**Argument.** The distance to a measure is a new definition. Fix $x$ and
let $\rho^\mu_x$ be the law of $\|y-x\|$ for $y\sim\mu$, a law on
$[0,\infty)$ with finite second moment. Its distribution function at
$r\ge0$ is $\mu(\overline B(x,r))$. For $u\in(0,1]$ the set
$\{r:u\le F_{\rho^\mu_x}(r)\}$ contains no negative $r$, so
$\delta_{\mu,u}(x)$ is the quantile $Q^\mu_x(u)$ of $\rho^\mu_x$. Thus
$d_{\mu,m}(x)=m^{-1/2}\|Q^\mu_x\|_{L^2(0,m)}$, and
$$|d_{\mu,m}(x)-d_{\nu,m}(x)|\le m^{-1/2}\|Q^\mu_x-Q^\nu_x\|_{L^2(0,m)}
\le m^{-1/2}\|Q^\mu_x-Q^\nu_x\|_{L^2(0,1)}
=m^{-1/2}W_2(\rho^\mu_x,\rho^\nu_x)$$
by the one-dimensional quantile formula. Finally, for every coupling $\pi$
of $\mu$ and $\nu$, the image coupling bounds
$W_2(\rho^\mu_x,\rho^\nu_x)$ by
$\|\,|\|y-x\|-\|y'-x\||\,\|_{L^2(\pi)}\le\|\,\|y-y'\|\,\|_{L^2(\pi)}$.
Taking the infimum over $\pi$ gives $W_2(\rho^\mu_x,\rho^\nu_x)\le
W_2(\mu,\nu)$ for every $x$.

**Library results.** `TauCeti.wassersteinEDist_eq_eLpNorm_quantile_sub` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Rearrangement.lean`;
`MeasureTheory.Measure.quantile` (the left-continuous inverse
$\inf\{x:t\le F(x)\}$) in `TauCeti/Probability/Quantile.lean`;
`TauCeti.wassersteinEDist_map_le_eLpNorm` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Pushforward.lean`;
`TauCeti.wassersteinEDist` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean`; the
triangle inequality in $L^2$, `MeasureTheory.eLpNorm_sub_le'` in
`Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean`.

### 108.42. Consistency of Brenier maps

**Statement.** Let $\mu\in\mathcal P_2(\mathbb R^d)$ be absolutely
continuous, let $\nu,\nu_n\in\mathcal P_2(\mathbb R^d)$ with
$W_2(\nu_n,\nu)\to0$, and let $T$, $T_n$ be the Brenier maps from $\mu$ to
$\nu$ and to $\nu_n$. Then $T_n\to T$ in $L^2(\mu)$. TauCeti has Brenier's
theorem, stability of the primal problem under varying marginals, and the
equivalence of weak convergence of graph plans with convergence in measure
of the maps; the conclusion, which also needs convergence of second moments
to pass from convergence in measure to $L^2(\mu)$, is not stated.

**Argument.** Let $\pi_n=(\mathrm{id},T_n)_\#\mu$ and
$\pi=(\mathrm{id},T)_\#\mu$, the unique optimal couplings by Brenier's
theorem. Convergence in $W_2$ gives $\nu_n\Rightarrow\nu$. By the triangle
inequality, $W_2(\mu,\nu_n)\to W_2(\mu,\nu)$, so the limsup hypothesis of
the stability theorem holds for the fixed lower semicontinuous cost
$\|x-y\|^2/2$. That theorem, on the Polish space $\mathbb R^d$, shows that
every subsequence of $(\pi_n)$ has a further subsequence converging weakly
to an optimal coupling of $\mu$ and $\nu$. By uniqueness this coupling is
$\pi$, so $\pi_n\Rightarrow\pi$. The graph-plan theorem converts this into
$T_n\to T$ in $\mu$-measure.

For $L^2$ convergence apply Vitali's theorem; it remains to show that
$(\|T_n\|^2)$ is uniformly integrable. First,
$\int\|T_n\|^2d\mu=W_2(\nu_n,\delta_0)^2\to W_2(\nu,\delta_0)^2=\int\|T\|^2d\mu$.
For $K>0$ the functions $\min(\|T_n\|^2,K)$ are bounded and converge in
measure to $\min(\|T\|^2,K)$, so their integrals converge. Subtracting,
$$\limsup_n\int(\|T_n\|^2-K)^+d\mu\le\int\|T\|^2d\mu-\int\min(\|T\|^2,K)\,d\mu,$$
which tends to $0$ as $K\to\infty$. Hence for every $\varepsilon$ there is
$K$ with $\int(\|T_n\|^2-K)^+\,d\mu<\varepsilon$ for all large $n$, and the
finitely many remaining $T_n$ are square integrable. Together this is
uniform integrability.

**Library results.** `TauCeti.exists_isKantorovichOptimalTransportMap_gradient`
and `TauCeti.IsOptimalCoupling.unique` in
`TauCeti/MeasureTheory/OptimalTransport/Brenier.lean`;
`TauCeti.exists_isOptimalCoupling_tendsto_of_polishSpace` and
`TauCeti.isCostLiminfStable_const` in
`TauCeti/MeasureTheory/OptimalTransport/Stability.lean`;
`TauCeti.tendsto_map_prodMk_self_iff_tendstoInMeasure` in
`TauCeti/MeasureTheory/OptimalTransport/GraphPlan/Convergence.lean`;
`TauCeti.WassersteinSpace.continuous_toProbabilityMeasure` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/WeakConvergence.lean`;
`TauCeti.wassersteinEDist_triangle` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean`;
`MeasureTheory.tendsto_Lp_finite_of_tendstoInMeasure` in
`Mathlib/MeasureTheory/Function/UniformIntegrable.lean`.

### 108.43. Gromov–Wasserstein distance

**Statement.** For $p\ge1$ and compact metric spaces with Borel
probabilities, put
$$\mathop{\mathrm{GW}}_p(\mu,\nu)^p=\inf_{\pi\in\Pi(\mu,\nu)}
\iint|d_X(x,x')-d_Y(y,y')|^p\,d\pi(x,y)\,d\pi(x',y').$$
Then $\mathop{\mathrm{GW}}_p$ is a metric on compact metric probability
spaces modulo measure-preserving isometries of their supports; in particular
$\mathop{\mathrm{GW}}_p(\mu,\nu)=0$ exactly when some isometry of
$\mathop{\mathrm{supp}}\mu$ onto $\mathop{\mathrm{supp}}\nu$ pushes $\mu$ to
$\nu$. TauCeti defines $\mathop{\mathrm{GW}}_p$ with this normalization,
proves it is an extended pseudodistance, proves that it vanishes exactly on
weakly isomorphic measured kernels (identified almost everywhere by a
coupling), and makes the measured kernels of finite $p$-size on standard
Borel probability spaces, modulo weak isomorphism, a metric space; missing is
the upgrade from weak isomorphism to an isometry of supports for compact
metric spaces.

**Argument.** Compact metric spaces are Polish, hence standard Borel and
second countable. Each probability is tight, and the distance kernels are
continuous. So TauCeti's triangle inequality and zero-distance
characterization apply, and $\mathop{\mathrm{GW}}_p$ is finite, at most
$\max(\mathop{\mathrm{diam}}X,\mathop{\mathrm{diam}}Y)$. It remains to
identify weak isomorphism with the existence of a measure-preserving
isometry of the supports.

If $f:\mathop{\mathrm{supp}}\mu\to\mathop{\mathrm{supp}}\nu$ is such an
isometry, extended measurably, the graph coupling $(\mathrm{id},f)_\#\mu$
identifies the kernels almost everywhere. Conversely let $\pi$ be a coupling
with $d_X(x,x')=d_Y(y,y')$ for $\pi\otimes\pi$-almost every pair. The set
where this fails is open, by continuity, and null, so it misses the support
of $\pi\otimes\pi$. That support contains $\Gamma\times\Gamma$ for
$\Gamma=\mathop{\mathrm{supp}}\pi$. Hence the equality holds on all of
$\Gamma\times\Gamma$. If $(x,y),(x,y')\in\Gamma$ then $d_Y(y,y')=0$, so
$\Gamma$ is the graph of a distance-preserving map $f$ defined on its
projection $\Gamma_X$. Since $\Gamma$ is compact, $\Gamma_X$ is closed, and
$\mu(\Gamma_X)\ge\pi(\Gamma)=1$, so $\Gamma_X\supseteq\mathop{\mathrm{supp}}\mu$.
Conversely, for $x\in\Gamma_X$ and a neighbourhood $U$ of $x$,
$\mu(U)=\pi(U\times Y)>0$, so $\Gamma_X\subseteq\mathop{\mathrm{supp}}\mu$.
Likewise the second projection of $\Gamma$ is $\mathop{\mathrm{supp}}\nu$,
so $f$ is onto. As $\pi$ is carried by the graph of $f$,
$\pi=(\mathrm{id},f)_\#\mu$ and $f_\#\mu=\nu$.

**Library results.** `TauCeti.gromovWassersteinEDist`,
`TauCeti.gromovWassersteinEDist_triangle` in
`TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Basic.lean`;
`TauCeti.gromovWassersteinEDist_eq_zero_iff_of_isTightMeasureSet` in
`TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Zero.lean`;
`TauCeti.AreWeaklyIsomorphicKernels`,
`TauCeti.areWeaklyIsomorphicKernels_comp_prodMap_of_hasLaw` and
`TauCeti.AreWeaklyIsomorphicKernels.gromovWassersteinEDist_eq_zero` in
`TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/WeakIsomorphism.lean`;
`MeasureTheory.isTightMeasureSet_singleton` in
`Mathlib/MeasureTheory/Measure/Tight.lean`; `MeasureTheory.Measure.support`,
`MeasureTheory.Measure.isClosed_support`,
`MeasureTheory.Measure.measure_compl_support` and
`MeasureTheory.Measure.support_subset_of_isClosed` in
`Mathlib/MeasureTheory/Measure/Support.lean`; for the quotient metric
structure, `TauCeti.GromovWassersteinSpace` in
`TauCeti/MeasureTheory/OptimalTransport/GromovWasserstein/Space.lean`.

### 108.44. Debiased Sinkhorn divergence

**Statement.** Let $X$ be a compact metric space, $\varepsilon>0$, and $c$ a
symmetric Lipschitz cost on $X\times X$ such that $e^{-c/\varepsilon}$ is a
positive definite universal kernel (for example quadratic cost on a compact
subset of $\mathbb R^d$). Then for probabilities on $X$,
$S_\varepsilon(\mu,\nu)\ge0$ with equality exactly when $\mu=\nu$, and
$S_\varepsilon(\mu_n,\mu)\to0$ if and only if $\mu_n\Rightarrow\mu$. TauCeti
defines $S_\varepsilon$ for costs with values in $[0,\infty]$ and proves the
first assertion for bounded measurable costs on a compact space whose Gibbs
kernel $e^{-c/\varepsilon}$ is jointly continuous and positive definite:
$S_\varepsilon(\mu,\nu)\ge0$, and, when the space is moreover compact
metrizable with its Borel $\sigma$-algebra and the Gibbs kernel is universal,
$S_\varepsilon(\mu,\nu)=0$ exactly when $\mu=\nu$. A real-valued Lipschitz
cost reduces to this case by adding a constant, a reduction that is not
stated. The metrization of weak convergence by $S_\varepsilon$ is absent, and
so is the universality of the Gaussian kernel needed for the quadratic-cost
example.

**Scope.** Nonnegativity and definiteness, for every cost satisfying the
stated hypotheses, are proved here. The metrization of weak convergence and
the quadratic-cost example remain gaps.

**Argument.** For a real-valued cost the entropic cost is the new definition
$\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)=\inf_\pi\bigl(\int c\,d\pi
+\varepsilon D(\pi\|\mu\otimes\nu)\bigr)$ over couplings. A Lipschitz
function on the compact space $X\times X$ is continuous and bounded; put
$a=-\min c$ and $c'=c+a$, a continuous cost with values in $[0,\infty)$,
bounded and measurable. For a coupling $\pi$ of probabilities,
$\int c'\,d\pi=\int c\,d\pi+a$, so the entropic costs for $c'$ and $c$ differ
by $a$ for every pair of probabilities. They are finite, since the product
coupling has divergence $0$ and bounded cost. In $S_\varepsilon$ the shifts
cancel, $a-\frac a2-\frac a2=0$, so the divergences for $c$ and $c'$ agree.
The Gibbs kernel of $c'$ is $e^{-a/\varepsilon}e^{-c/\varepsilon}$, a
positive multiple of that of $c$. It is therefore positive definite, and it
is universal because scaling the sections by a positive constant does not
change their span. It is jointly continuous by TauCeti's continuity lemma for
a continuous finite cost. A compact metric space carries its Borel
$\sigma$-algebra and approximates closed sets from outside, being
metrizable. TauCeti's two theorems therefore apply to $c'$ and give
$S_\varepsilon(\mu,\nu)\ge0$ and $S_\varepsilon(\mu,\nu)=0\iff\mu=\nu$.
The symmetry of $c$ is not used beyond the symmetry of the positive definite
Gibbs kernel.

**Library results.** `TauCeti.sinkhornDivergence`,
`TauCeti.sinkhornDivergence_nonneg` and `TauCeti.sinkhornDivergence_eq_zero_iff`
in `TauCeti/MeasureTheory/OptimalTransport/Entropic/SinkhornDivergence.lean`;
`TauCeti.entropicTransportCost` in
`TauCeti/MeasureTheory/OptimalTransport/Entropic/Basic.lean`;
`TauCeti.entropicGibbsKernel` and `TauCeti.continuous_entropicGibbsKernel` in
`TauCeti/MeasureTheory/OptimalTransport/Entropic/Duality.lean`;
`TauCeti.IsUniversalKernel` in
`TauCeti/Analysis/PositiveDefinite/Kernel/Universal.lean`;
`InformationTheory.klDiv_self` in
`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`; the instance
`HasOuterApproxClosed` for pseudometrizable spaces in
`Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean`.

### 108.46. Gaussian transport and barycenters

**Statement.** For covariance matrices $A,B\ge0$,
$$W_2^2(N(m,A),N(n,B))=\|m-n\|^2+\mathop{\mathrm{tr}}
[A+B-2(A^{1/2}BA^{1/2})^{1/2}],$$
and if $A>0$ the optimal map is
$x\mapsto n+A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}(x-m)$. For finitely many
Gaussian laws $N(m_i,A_i)$ with $A_i>0$ and weights $\lambda_i\ge0$ summing
to one, the barycenter is unique and Gaussian, with mean $\sum_i\lambda_im_i$
and covariance the unique positive definite solution of
$$\bar A=\sum_i\lambda_i(\bar A^{1/2}A_i\bar A^{1/2})^{1/2};$$
if the $A_i$ commute, $\bar A=(\sum_i\lambda_iA_i^{1/2})^2$. TauCeti proves
the distance formula and optimal affine map when $A$ is positive definite,
and the barycenter of two Gaussian laws through the geodesic. For finitely
many Gaussian laws with positive semidefinite covariances it proves that, if
a positive definite $\bar A$ solves the fixed-point equation, the Gaussian
law with mean $\sum_i\lambda_im_i$ and covariance $\bar A$ is a barycenter,
the only one when some covariance with positive weight is positive definite.
Missing are the distance formula with both covariances singular, the
existence of a positive definite solution of the fixed-point equation, and
the commuting case; the uniqueness of the solution follows from the
uniqueness of the barycenter.

**Scope.** The uniqueness of a positive definite solution of the fixed-point
equation, and the commuting case, with the barycenter unique and Gaussian of
covariance $(\sum_i\lambda_iA_i^{1/2})^2$, are proved here. The existence of
a positive definite solution for noncommuting covariances, and with it the
Gaussian form of the barycenter in general, and the distance formula with
both covariances singular remain gaps.

**Argument.** Some $\lambda_{i_0}$ is positive, and $A_{i_0}$ is positive
definite, so TauCeti's uniqueness theorem applies. If $S$ and $S'$ are
positive definite solutions, the set of barycenters is both
$\{N(\bar m,S)\}$ and $\{N(\bar m,S')\}$, with $\bar m=\sum_i\lambda_im_i$.
The two Gaussian laws are equal, and so are their covariance matrices,
$S=S'$.

Let the $A_i$ commute. A matrix commuting with $A_i$ commutes with its square
root, which is a continuous function of $A_i$. Hence all $A_i$ and
$A_j^{1/2}$ commute pairwise, and they commute with
$T=\sum_i\lambda_iA_i^{1/2}$. Since $A_{i_0}^{1/2}$ is positive definite and
the other terms are positive semidefinite, $T$ is positive definite. Put
$S=T^2$, positive definite with $S^{1/2}=T$ by uniqueness of positive square
roots. For each $i$, $TA_i^{1/2}$ is positive semidefinite as a product of
commuting positive semidefinite matrices, and
$(TA_i^{1/2})^2=TA_iT=S^{1/2}A_iS^{1/2}$. By uniqueness of square roots
again, $(S^{1/2}A_iS^{1/2})^{1/2}=TA_i^{1/2}$, and
$$\sum_i\lambda_i(S^{1/2}A_iS^{1/2})^{1/2}=T\sum_i\lambda_iA_i^{1/2}=T^2=S .$$
So $S$ solves the fixed-point equation, and TauCeti's two theorems make
$N(\bar m,S)$ the unique barycenter.

**Library results.**
`TauCeti.Probability.isFrechetBarycenter_sum_smul_dirac_multivariateGaussian`
and `TauCeti.Probability.frechetBarycenters_sum_smul_dirac_multivariateGaussian`
in `TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/FixedPoint.lean`;
`TauCeti.Probability.gaussianWassersteinLaw` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Gaussian/Barycenter.lean`;
`TauCeti.Probability.covMatrix_multivariateGaussian` in
`TauCeti/Probability/Distributions/Gaussian/Multivariate.lean`;
`CFC.sqrt`, `CFC.sqrt_unique` and `CFC.sqrt_mul_sqrt_self` in
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Basic.lean`;
`Commute.cfcₙ_nnreal` in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Commute.lean`;
`Commute.mul_nonneg` in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Instances.lean`;
`Matrix.nonneg_iff_posSemidef` in `Mathlib/Analysis/Matrix/Order.lean`.

### 108.50. Minimax lower bounds for transport estimation

**Statement.** Let $d\ge3$ and let $\lambda$ be the uniform law on
$[0,1]^d$. Every probability supported on at most $n$ points is at
$W_1$-distance at least $n^{-1/d}/(108\,d)$ from $\lambda$. For $n\ge8$ and
every estimator $\tilde\mu_n$, that is, every measurable function of $n$
independent observations,
$\sup_\mu\mathbb E_\mu W_1(\tilde\mu_n,\mu)\ge\frac1{16}(2n)^{-1/d}$, the
supremum over probabilities supported in $[0,1]^d$. TauCeti defines the
$N$-point Wasserstein quantization error and proves that best quantizers
exist on proper spaces; no quantitative bound and no minimax framework are
present.

**Scope.** The first, deterministic bound is proved here, in fact with
$n^{-1/d}/8$ and for every $d\ge1$. The minimax bound remains a gap.

**Argument.** Let $\nu$ be carried by a set $S$ of at most $n$ points. For
every coupling $\pi$ of $\lambda$ and $\nu$, the second coordinate lies in
$S$ almost surely, so
$\int\|x-y\|\,d\pi\ge\int\mathop{\mathrm{dist}}(x,S)\,d\lambda(x)$. Hence
$W_1(\lambda,\nu)\ge\int\mathop{\mathrm{dist}}(x,S)\,d\lambda$; this is also
TauCeti's reduction of the quantization error. Each Euclidean ball of radius
$r$ lies in a cube of side $2r$, so
$\lambda\{x:\mathop{\mathrm{dist}}(x,S)<r\}\le n(2r)^d$. By Markov's
inequality,
$$\int\mathop{\mathrm{dist}}(x,S)\,d\lambda\ge r\bigl(1-n(2r)^d\bigr).$$
With $r=\frac12(2n)^{-1/d}$ the bracket is $\frac12$, and the bound is
$\frac14(2n)^{-1/d}\ge n^{-1/d}/8\ge n^{-1/d}/(108\,d)$.

**Library results.** `TauCeti.wassersteinQuantizationError` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/FiniteSupport.lean` and
`TauCeti.wassersteinQuantizationError_eq_iInf_eLpNorm_infEDist` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Quantization.lean`;
`TauCeti.wassersteinEDist` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean`;
`Real.volume_pi_ball` in `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
and `PiLp.volume_preserving_ofLp` in
`Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`;
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` in
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.

### 108.51. Smooth laws and smoothed distances

**Statement.** Let $d\ge3$, let $\mu$ have a density on $\mathbb T^d$ with
$H^s$ norm at most $L$, and let $\tilde\mu_n$ be the signed measure obtained
by truncating the empirical Fourier series at frequencies $\|m\|\le M$, with
$M\asymp n^{1/(d+2s)}$. Then
$\mathbb E\widetilde W_1(\tilde\mu_n,\mu)\le Cn^{-(s+1)/(d+2s)}$, with $C$
depending only on $d,s,L$ and the constant in $M\asymp n^{1/(d+2s)}$, and a
probability $\bar\mu_n$ minimizing $\widetilde W_1(\cdot,\tilde\mu_n)$
satisfies $W_1(\bar\mu_n,\mu)\le2\widetilde W_1(\tilde\mu_n,\mu)$. For any
$d\ge1$ and $\mu$ supported in $[-1,1]^d$,
$\mathbb E W_1^{(\sigma)}(\mu_n,\mu)\le C_{\sigma,d}\,n^{-1/2}$. TauCeti
proves that convolution with a common law does not increase $W_p$; the
smoothed distance, its rate, and the torus estimator are absent.

**Scope.** The projection inequality
$W_1(\bar\mu_n,\mu)\le2\widetilde W_1(\tilde\mu_n,\mu)$ is proved here. The
two rates remain gaps.

**Argument.** $\widetilde W_1$ is a new definition. As a supremum of the
absolute values of linear functionals, it satisfies the triangle inequality
on signed measures; for each $f$, also $-f$ is admissible. The torus is a
compact metric space, so Kantorovich–Rubinstein duality gives
$W_1=\widetilde W_1$ on probabilities. Since $\mu$ itself is a candidate in
the minimization,
$$W_1(\bar\mu_n,\mu)=\widetilde W_1(\bar\mu_n,\mu)
\le\widetilde W_1(\bar\mu_n,\tilde\mu_n)+\widetilde W_1(\tilde\mu_n,\mu)
\le2\widetilde W_1(\tilde\mu_n,\mu).$$
Existence of $\bar\mu_n$ is part of the hypothesis.

**Library results.** `TauCeti.wassersteinEDist_one_eq_iSup_of_compactSpace`
in `TauCeti/MeasureTheory/OptimalTransport/Wasserstein/KantorovichRubinstein.lean`;
`AddCircle` and its compactness in `Mathlib/Topology/Instances/AddCircle/Defs.lean`.

### 108.56. Semidiscrete dual

**Statement.** The function $E(g)=\int g^c\,d\mu+\sum_jb_jg_j$ is concave,
invariant under adding a constant to all $g_j$, and continuously
differentiable with $\partial E/\partial g_j=b_j-\mu(L_j(g))$; its maximum
is the optimal transport cost from $\mu$ to $\nu$. A vector $g$ is a
maximizer exactly when $\mu(L_j(g))=b_j$ for all $j$, and then the map
sending $L_j(g)$ to $y_j$ is the optimal transport map. TauCeti has the
general $c$-transform and dual attainment; Laguerre cells, the
differentiability of $E$, and the semidiscrete characterization are absent.

**Argument.** Laguerre cells and $E$ are new definitions. Since
$\mu\in\mathcal P_2$, each $c(\cdot,y_j)$ is integrable, and so is $g^c$.
As a minimum of affine functions of $g$, $g^c(x)$ is concave in $g$, so $E$
is concave. Adding $t$ to all $g_j$ lowers $g^c$ by $t$ and raises
$\sum_jb_jg_j$ by $t$. Moreover $|g^c(x)-g'^c(x)|\le\|g-g'\|_\infty$.

*Ties are null.* For $j\ne k$ the set where
$c(x,y_j)-g_j=c(x,y_k)-g_k$ is
$\{2\langle x,y_k-y_j\rangle=\mathrm{const}\}$, a hyperplane because
$y_j\ne y_k$. It is Lebesgue-null, hence $\mu$-null. So $\mu$-almost every
$x$ has a unique index $j(x)$ with $x\in L_{j(x)}(g)$.

*Derivative.* Let $A_h$ be the set of $x$ at which the two smallest values
of $c(x,y_j)-g_j$ differ by less than $2\|h\|_\infty$. Off $A_h$,
$(g+h)^c(x)=g^c(x)-h_{j(x)}$, and on $A_h$ the two sides differ by at most
$2\|h\|_\infty$. Hence
$$\Bigl|E(g+h)-E(g)-\sum_jh_j\bigl(b_j-\mu(L_j(g))\bigr)\Bigr|
\le2\|h\|_\infty\,\mu(A_h).$$
As $h\to0$ the sets $A_h$ decrease to the null tie set, so $\mu(A_h)\to0$
and $E$ is differentiable with the stated gradient. If $g^{(k)}\to g$, the
indicators of $L_j(g^{(k)})$ converge to that of $L_j(g)$ off the tie set,
and dominated convergence gives continuity of the gradient.

*Maximizers and duality.* For every coupling $\pi$ of $\mu$ and $\nu$,
$c(x,y_j)\ge g^c(x)+g_j$ gives $\int c\,d\pi\ge E(g)$, so $E\le\mathrm{OT}$.
Taking $k$ with $g_k=\max g$,
$$E(g)\le\int c(x,y_k)\,d\mu+\sum_jb_j(g_j-g_k)
\le C-\min_jb_j\,(\max g-\min g),$$
so on the slice $\{g_m=0\}$ the superlevel sets of the continuous function
$E$ are compact, and a maximizer exists. At a maximizer the gradient
vanishes, $\mu(L_j(g))=b_j$. Conversely, if $\mu(L_j(g))=b_j$ for all $j$,
concavity along segments with zero derivative at $g$ makes $g$ a maximizer.
In that case the map $T$ with $T=y_j$ on $L_j(g)$, defined off the tie set,
pushes $\mu$ to $\nu$, and
$$\int c(x,T(x))\,d\mu=\sum_j\int_{L_j(g)}(g^c(x)+g_j)\,d\mu=E(g)\le\mathrm{OT}.$$
So $T$ is optimal and $\max E=\mathrm{OT}$.

**Library results.** `MeasureTheory.Measure.addHaar_affineSubspace` in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`;
`MeasureTheory.tendsto_integral_of_dominated_convergence` in
`Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`;
`IsCompact.exists_isMaxOn` in `Mathlib/Topology/Order/Compact.lean`;
`TauCeti.IsCoupling` in `TauCeti/MeasureTheory/OptimalTransport/Coupling.lean`,
`TauCeti.transportCost` in `TauCeti/MeasureTheory/OptimalTransport/Cost/Basic.lean`
and `TauCeti.IsKantorovichOptimalTransportMap` in
`TauCeti/MeasureTheory/OptimalTransport/Monge.lean`.

### 108.57. Tangent-space linearization

**Statement.** For absolutely continuous $\gamma$,
$\|\log_\gamma\mu\|_{L^2(\gamma)}=W_2(\gamma,\mu)$,
$s\mapsto\exp_\gamma(s\log_\gamma\mu)$, $0\le s\le1$, is the constant-speed
geodesic from $\gamma$ to $\mu$, and
$W_2(\mu,\nu)\le\|\log_\gamma\mu-\log_\gamma\nu\|_{L^2(\gamma)}$. On a
compatible family containing $\gamma$ equality holds, so $\log_\gamma$ is an
isometric embedding into a Hilbert space, and the Fréchet mean of compatible
$\mu_1,\ldots,\mu_N$ is $(N^{-1}\sum_it_\gamma^{\mu_i})_\#\gamma$. A family
of centered nondegenerate Gaussian laws containing the standard Gaussian is
compatible exactly when the covariances commute. TauCeti defines the tangent
space as a closure of gradients, proves the coupling bound through
pushforwards, the displacement geodesics, and the one-dimensional quantile
isometry; missing are the log and exponential maps as such, compatibility,
the isometric embedding with the barycenter formula, and the Gaussian
criterion.

**Scope.** The norm identity, the geodesic, the inequality, and the
isometric embedding on compatible families are proved here. The barycenter
formula and the Gaussian criterion remain gaps.

**Argument.** The maps $\log_\gamma$ and $\exp_\gamma$ and compatibility
are new definitions, with $t_\gamma^\mu$ the Brenier map, unique
$\gamma$-almost everywhere. Its graph coupling is optimal, so
$\|t_\gamma^\mu-\mathrm{id}\|_{L^2(\gamma)}^2=W_2(\gamma,\mu)^2$. The law of
$(1-s)x+sy$ under this optimal coupling is
$\exp_\gamma(s\log_\gamma\mu)$, and TauCeti's interpolation theorem makes
these laws a geodesic segment. Pushing $\gamma$ forward under the pair
$(t_\gamma^\mu,t_\gamma^\nu)$ gives a coupling of $\mu$ and $\nu$, whence
the inequality.

For equality on a compatible family $\mathcal C\ni\gamma$, take
$\mu,\nu\in\mathcal C$, so $\nu$ is absolutely continuous. The identity is
optimal from $\nu$ to $\nu$, with cost $0$, so $t_\nu^\nu=\mathrm{id}$
$\nu$-almost everywhere. Since $\gamma=(t_\nu^\gamma)_\#\nu$, compatibility
for the triples $(\mu,\gamma,\nu)$ and $(\nu,\gamma,\nu)$ gives
$$\|t_\gamma^\mu-t_\gamma^\nu\|_{L^2(\gamma)}^2
=\int\|t_\gamma^\mu(t_\nu^\gamma x)-t_\gamma^\nu(t_\nu^\gamma x)\|^2\,d\nu
=\int\|t_\nu^\mu(x)-x\|^2\,d\nu=W_2(\mu,\nu)^2 .$$

**Library results.** `TauCeti.exists_isKantorovichOptimalTransportMap_gradient`
and `TauCeti.IsOptimalCoupling.unique` in
`TauCeti/MeasureTheory/OptimalTransport/Brenier.lean`;
`TauCeti.WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Geodesic/Basic.lean`;
`TauCeti.wassersteinEDist_map_le_eLpNorm` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Pushforward.lean`;
`TauCeti.wassersteinTangentSpace` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/TangentSpace.lean`;
`MeasureTheory.integral_map` for the change of variables.

### 108.59. Procrustes iteration for barycenters

**Statement.** From an absolutely continuous $\gamma_0$ put
$\gamma_{j+1}=(N^{-1}\sum_it_{\gamma_j}^{\mu_i})_\#\gamma_j
=\exp_{\gamma_j}(-F'(\gamma_j))$. For absolutely continuous $\gamma$ and
$\tau\in[0,1]$, $\gamma_\tau=\exp_\gamma(-\tau F'(\gamma))$ is absolutely
continuous and
$F(\gamma_\tau)-F(\gamma)\le-\|F'(\gamma)\|_{L^2(\gamma)}^2(\tau-\tau^2/2)$.
If one $\mu_i$ has a bounded density, the iterates stay in a $W_2$-compact
set and every limit point is a Karcher mean; if moreover $F$ has a unique
stationary point, $W_2(\gamma_j,\bar\mu)\to0$ for the Fréchet mean
$\bar\mu$, and $t_{\gamma_j}^{\mu_i}\to t_{\bar\mu}^{\mu_i}$ uniformly on
compact subsets of a set of full $\bar\mu$-measure. For centered Gaussian
$\mu_i$ with one covariance nonsingular and a nonsingular centered Gaussian
$\gamma_0$, the iterates converge to the Gaussian barycenter of 108.46.
Absent from all three libraries.

**Scope.** The descent inequality, with
$F'(\gamma)=-N^{-1}\sum_i(t_\gamma^{\mu_i}-\mathrm{id})$ taken as a
definition, is proved here. Absolute continuity of $\gamma_\tau$, the
convergence statements, and the Gaussian case remain gaps.

**Argument.** Write $t_i=t_\gamma^{\mu_i}$, $\bar t=N^{-1}\sum_it_i$ and
$w=\bar t-\mathrm{id}=-F'(\gamma)$, so $\gamma_\tau=(\mathrm{id}+\tau w)_\#\gamma$.
Pushing $\gamma$ forward under $(\mathrm{id}+\tau w,t_i)$ gives a coupling
of $\gamma_\tau$ and $\mu_i$, so
$$W_2^2(\gamma_\tau,\mu_i)\le\|\mathrm{id}-t_i+\tau w\|^2
=W_2^2(\gamma,\mu_i)+2\tau\langle w,\mathrm{id}-t_i\rangle+\tau^2\|w\|^2,$$
in $L^2(\gamma)$, using $\|\mathrm{id}-t_i\|^2=W_2^2(\gamma,\mu_i)$. Average
over $i$ and divide by $2$. Since $N^{-1}\sum_i(\mathrm{id}-t_i)=-w$,
$$F(\gamma_\tau)\le F(\gamma)-\tau\|w\|^2+\tfrac{\tau^2}2\|w\|^2 .$$
The inequality holds for every real $\tau$; the restriction $\tau\in[0,1]$
matters only for absolute continuity.

**Library results.** `TauCeti.wassersteinEDist_map_le_eLpNorm` in
`TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Pushforward.lean`;
`TauCeti.exists_isKantorovichOptimalTransportMap_gradient` in
`TauCeti/MeasureTheory/OptimalTransport/Brenier.lean`; the inner product on
`MeasureTheory.Lp` in `Mathlib/MeasureTheory/Function/L2Space.lean`.

### 108.68. Criteria for characteristic kernels

**Statement.** For a bounded measurable kernel, there are probabilities
$\mu\ne\nu$ with $\mathop{\mathrm{MMD}}(\mu,\nu)=0$ exactly when some finite
nonzero signed measure $\eta$ of total mass zero has
$\iint k\,d\eta\,d\eta=0$. Hence: (a) integrally strictly positive definite
kernels are characteristic, for example the Gaussian, Laplace, and inverse
multiquadric kernels $(c^2+\|x-y\|^2)^{-\beta}$, $c,\beta>0$, on
$\mathbb R^d$; (b) universal kernels on compact metric spaces are
characteristic; (c) for $k(x,y)=\psi(x-y)$ with $\psi$ bounded, continuous,
and positive definite on $\mathbb R^d$ with spectral measure $\Lambda$, $k$
is characteristic if and only if $\mathop{\mathrm{supp}}\Lambda=\mathbb R^d$;
in particular every nonzero such $\psi$ of compact support is
characteristic, and the sinc kernel is not; (d) for the unbounded kernel $k(x,y)=(1+x^\top y)^2$ and laws with finite
fourth moments, $\mathop{\mathrm{MMD}}^2(\mu,\nu)=2\|m_\mu-m_\nu\|^2
+\|\Sigma_\mu-\Sigma_\nu+m_\mu m_\mu^\top-m_\nu m_\nu^\top\|_F^2$, which
vanishes for distinct laws with equal first two moments. TauCeti proves (b)
on compact metrizable spaces, Bochner's theorem, and positive definiteness
of the Gaussian kernel, and Mathlib has Fourier uniqueness of finite
measures; the general criterion, (a), the spectral characterization (c), and
the example (d) are absent.

**Scope.** The general criterion, the implication in (a) without the named
examples, and the identity in (d) are proved here. In (d) the kernel is
unbounded, which is why the statement assumes finite fourth moments. The
examples in (a) and the spectral characterization (c) remain gaps.

**Argument.** Assume the feature map is Bochner integrable for the
probabilities considered; this holds for a bounded kernel whose feature map
is strongly measurable. TauCeti's identity gives
$\mathop{\mathrm{MMD}}^2(\mu,\nu)=\iint k\,d(\mu-\nu)\,d(\mu-\nu)$. If
$\mu\ne\nu$ have $\mathop{\mathrm{MMD}}=0$, take $\eta=\mu-\nu$. Conversely,
let $\eta\ne0$ have mass zero and $\iint k\,d\eta\,d\eta=0$, with Jordan
decomposition $\eta=\eta^+-\eta^-$. Both parts have the same mass $m>0$,
and $\mu=\eta^+/m$, $\nu=\eta^-/m$ are distinct probabilities with
$\mathop{\mathrm{MMD}}^2(\mu,\nu)=m^{-2}\iint k\,d\eta\,d\eta=0$. For an
integrally strictly positive definite kernel no such $\eta$ exists, which
is (a).

For (d), $(1+x^\top y)^2=1+2x^\top y+\langle xx^\top,yy^\top\rangle_F$. With
finite fourth moments every term is integrable for products of the laws.
In the double integral against $(\mu-\nu)^{\otimes2}$ the constant
contributes $0$, the second term $2\|m_\mu-m_\nu\|^2$, and the third
$\|\mathbb E_\mu XX^\top-\mathbb E_\nu YY^\top\|_F^2$; and
$\mathbb E_\mu XX^\top=\Sigma_\mu+m_\mu m_\mu^\top$. For example, $N(0,1)$
and the uniform law on $\{-1,1\}$ are distinct with equal first two
moments.

**Library results.** `Matrix.PosSemidef.kernelMeanEmbedding` and
`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq` in
`TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean`;
`MeasureTheory.SignedMeasure.toJordanDecomposition` in
`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`; Fubini in
`Mathlib/MeasureTheory/Integral/Prod.lean`.

### 108.70. Metrization of weak convergence

**Statement.** For a bounded continuous characteristic kernel on a Polish
space, $\mu_n\Rightarrow\mu$ implies $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$;
conversely, if $(\mu_n)$ is tight and $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$,
then $\mu_n\Rightarrow\mu$. Without tightness: (a) on a compact metric space
the MMD of a continuous universal kernel metrizes the weak topology on
probabilities; (b) on $\mathbb R^d$, if $k(x,y)=\psi(x-y)$ with
$\psi\in C_0\cap L^1$ real, bounded and strictly positive definite, and
$\int(\hat\psi(\omega)(1+\|\omega\|^2)^l)^{-1}\,d\omega<\infty$ for some
integer $l$, the MMD metrizes weak convergence (this covers the Matérn
family but not the Gaussian kernel). Mathlib's Prokhorov theorem and
TauCeti's kernel mean embedding with its double-integral formula give the
tight case by a short subsequence argument, and the forward implication
follows from weak convergence of $\mu_n\otimes\mu_n$ against the bounded
continuous $k$. TauCeti characterizes weak convergence on Polish spaces by
uniform convergence of integrals of bounded $1$-Lipschitz functions and by
truncated transport costs, but MMD is not defined on probability measures in
any of the three libraries, and the metrization statements (a) and (b) are
absent.

**Scope.** The forward implication and the converse for tight sequences are
proved here. The metrization statements (a) and (b) remain gaps.

**Argument.** Define $\mathop{\mathrm{MMD}}$ as the distance of mean
embeddings; on a Polish space the feature map of a bounded continuous kernel
is continuous into a separable space, hence Bochner integrable. By TauCeti's
identity and Fubini,
$$\mathop{\mathrm{MMD}}^2(\mu_n,\mu)=\int k\,d(\mu_n\otimes\mu_n)
-2\int k\,d(\mu_n\otimes\mu)+\int k\,d(\mu\otimes\mu).$$
If $\mu_n\Rightarrow\mu$, then $\mu_n\otimes\mu_n\Rightarrow\mu\otimes\mu$
and $\mu_n\otimes\mu\Rightarrow\mu\otimes\mu$, and $k$ is bounded and
continuous, so the right side tends to $0$.

If $(\mu_n)$ is tight, Prokhorov's theorem makes its closure compact. Every
subsequence has a further subsequence converging weakly to some $\nu$. Along
it, $\mathop{\mathrm{MMD}}(\mu_{n'},\nu)\to0$ by the first part. Together
with $\mathop{\mathrm{MMD}}(\mu_{n'},\mu)\to0$ and the triangle inequality
in the Hilbert space, $\mathop{\mathrm{MMD}}(\nu,\mu)=0$, so $\nu=\mu$
because $k$ is characteristic. As every subsequence has a further
subsequence converging to $\mu$, $\mu_n\Rightarrow\mu$.

**Library results.** `Matrix.PosSemidef.kernelMeanEmbedding` and
`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq` in
`TauCeti/Analysis/PositiveDefinite/Kernel/MeanEmbedding.lean`;
`MeasureTheory.ProbabilityMeasure.continuous_prod` in
`Mathlib/MeasureTheory/Measure/FiniteMeasureProd.lean`;
`isCompact_closure_of_isTightMeasureSet` in
`Mathlib/MeasureTheory/Measure/Prokhorov.lean`;
`MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` in
`Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean`.

### 108.74. Random Fourier features

**Statement.** Let $k(x,y)=\psi(x-y)$ be continuous and positive definite on
$\mathbb R^d$ with $\psi(0)=1$, so its spectral measure $\Lambda$ is a
probability. Let $\omega_1,\ldots,\omega_D\sim\Lambda$ and
$b_1,\ldots,b_D$ uniform on $[0,2\pi]$ be independent, and put
$z(x)=\sqrt{2/D}\,(\cos(\omega_j^\top x+b_j))_{j\le D}$. Then
$\mathbb E\,z(x)^\top z(y)=k(x,y)$, and for fixed $x,y$,
$\mathbb P(|z(x)^\top z(y)-k(x,y)|\ge\varepsilon)\le2e^{-D\varepsilon^2/8}$.
If $\sigma^2=\int\|\omega\|^2\Lambda(d\omega)<\infty$ and
$M\subset\mathbb R^d$ is compact with $\sigma\mathop{\mathrm{diam}}M\ge
\varepsilon$, then
$$\mathbb P\Bigl(\sup_{x,y\in M}|z(x)^\top z(y)-k(x,y)|\ge\varepsilon\Bigr)
\le98\Bigl(\frac{\sigma\mathop{\mathrm{diam}}M}{\varepsilon}\Bigr)^2
\exp\Bigl(-\frac{D\varepsilon^2}{32(d+1)}\Bigr),$$
and on the event that this supremum is below $\varepsilon$,
$|\mathop{\mathrm{MMD}}_z(\mu,\nu)^2-\mathop{\mathrm{MMD}}_k(\mu,\nu)^2|
\le4\varepsilon$ for all probabilities $\mu,\nu$ on $M$, where
$\mathop{\mathrm{MMD}}_z(\mu,\nu)^2=\|\int z\,d\mu-\int z\,d\nu\|^2$.
TauCeti's probability form of Bochner's theorem gives the unbiasedness
identity by a product-to-sum computation, and Mathlib's Hoeffding inequality
then gives the pointwise bound, since each summand of $z(x)^\top z(y)$ is
$D^{-1}$ times a variable in $[-2,2]$; neither is stated. The uniform bound
needs a net argument on $M\times M$ with a Lipschitz control of the error;
TauCeti's volumetric bound on covering numbers of bounded sets in
finite-dimensional normed spaces supplies the nets, and the argument is
absent.

**Scope.** The unbiasedness identity, the pointwise bound, and the MMD
comparison on the event are proved here. The uniform bound remains a gap.
The kernel is real-valued here, as the statement implies, so $\psi$ is real
and even.

**Argument.** Bochner's theorem gives
$\psi(t)=\int e^{i\langle\omega,t\rangle}\Lambda(d\omega)$, and since $\psi$
is real, $\psi(t)=\int\cos\langle\omega,t\rangle\,\Lambda(d\omega)$. By the
product-to-sum formula, with $a=\omega^\top x+b$ and $a'=\omega^\top y+b$,
$$2\cos a\cos a'=\cos(\omega^\top(x-y))+\cos(\omega^\top(x+y)+2b).$$
The second term has mean zero over $b$ uniform on $[0,2\pi]$, for every
$\omega$. Integrating over $\omega$ gives $\mathbb E[2\cos a\cos a']=k(x,y)$,
and $z(x)^\top z(y)$ is the average of $D$ independent copies. Each copy lies
in $[-2,2]$, so Hoeffding's inequality, with variance proxy $(4/2)^2=4$ per
summand, gives
$$\mathbb P\Bigl(\Bigl|\sum_j(V_j-\mathbb EV_j)\Bigr|\ge D\varepsilon\Bigr)
\le2\exp\Bigl(-\frac{D^2\varepsilon^2}{8D}\Bigr)=2e^{-D\varepsilon^2/8}.$$
On the event, both MMDs are double integrals against $(\mu-\nu)^{\otimes2}$,
of $z(x)^\top z(y)$ and of $k$. Their difference is bounded by
$\varepsilon\,|\mu-\nu|(M)^2\le4\varepsilon$.

**Library results.** `TauCeti.bochner_probabilityMeasure` in
`TauCeti/Analysis/Bochner/BochnerTheorem.lean`;
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` and
`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun` in
`Mathlib/Probability/Moments/SubGaussian.lean`; `Real.cos_add` and
`Real.cos_sub` in `Mathlib/Analysis/Complex/Trigonometric.lean`, with the
integral of $\cos$ over a period from `integral_cos` in
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`.
