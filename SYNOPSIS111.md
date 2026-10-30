# Synopsis: Optimal transport and kernel discrepancies

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-111).

This synopsis follows Section 111. Subdivision 111A records the statistical
uses of Wasserstein distance. Subdivision 111B records kernel discrepancies.
Existence of optimal plans, Kantorovich duality, cyclical monotonicity,
completeness of $W_p$, the Kantorovich–Rubinstein formula, the
one-dimensional quantile coupling, Brenier's theorem, displacement
interpolation, the Benamou–Brenier formula, and entropic transport are
[CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md), items 39–49 and 90. The heat
flow as a Wasserstein gradient flow is item 62 of that file. The representer theorem is [SYNOPSIS104](SYNOPSIS104.md), item 8, and the
Hilbertian central limit theorem is item 20 of that file. Kernel Rademacher
complexity is [SYNOPSIS107](SYNOPSIS107.md), item 9.

Throughout, for $p\ge1$, $W_p$ is the $p$-Wasserstein distance on the space
$\mathcal P_p$ of Borel probabilities with finite $p$th moment, as in
CKMA SYNOPSIS39.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-111a"></a>

## 111A. Optimal Transport, Wasserstein Distances, and Their Statistics

Let $\mu_n$ be the empirical measure of $n$ independent copies of a
probability $\mu$ on $\mathbb R^d$.

* **1. Empirical Wasserstein bounds.** For a probability supported in
  a fixed bounded subset of $\mathbb R^d$ and $p\ge1$,
  $$\mathbb E W_p^p(\mu_n,\mu)\le C
  \begin{cases}n^{-1/2},&p>d/2,\\
  n^{-1/2}\log(1+n),&p=d/2,\\
  n^{-p/d},&p<d/2.
  \end{cases}$$
  If only a finite $q$th moment is assumed, $q>p$, the usual
  Fournier–Guillin bound adds $C n^{-(q-p)/q}$, away from the critical
  cases $q=2p$ for $p\ge d/2$ and $q=dp/(d-p)$ for $p<d/2$,
  where logarithmic modifications are needed. These are upper bounds,
  not the exact rate for every distribution. Smooth one-dimensional
  laws can converge faster, whereas atoms can attain slower rates.

Let $\mu_1,\ldots,\mu_K\in\mathcal P_2(\mathbb R^d)$ and let
$\lambda_i>0$ sum to one. A **Wasserstein barycenter** minimizes
$\mu\mapsto\sum_{i=1}^K\lambda_i W_2^2(\mu,\mu_i)$.

* **2. Uniqueness of the barycenter.** If at least one $\mu_i$ is
  absolutely continuous, the barycenter exists and is unique.

* **3. Consistency of Brenier maps.** Let $\mu\in\mathcal P_2(\mathbb R^d)$
  be absolutely continuous and let $\nu,\nu_n\in\mathcal P_2(\mathbb R^d)$
  satisfy $W_2(\nu_n,\nu)\to0$. Let $T$ and $T_n$ be the Brenier maps pushing
  $\mu$ forward to $\nu$ and to $\nu_n$, in the sense of CKMA SYNOPSIS39,
  item 46. Then $T_n\to T$ in $L^2(\mu)$. A quantitative comparison of map
  error and target-measure error requires additional regularity; this
  consistency theorem supplies no universal rate.

A **metric measure space** is a complete separable metric space equipped
with a Borel probability. For $p\ge1$ and probabilities of finite $p$th
moment, the **Gromov–Wasserstein distance** of order $p$ is
$$
\mathop{\mathrm{GW}}_p(\mu,\nu)^p
=\inf_{\pi\in\Pi(\mu,\nu)}
\iint \bigl|d_X(x,x')-d_Y(y,y')\bigr|^p\,d\pi(x,y)\,d\pi(x',y').
$$

* **4. Gromov–Wasserstein distance.** With the normalization above,
  $\mathop{\mathrm{GW}}_p$ is a metric on compact metric probability
  spaces modulo measure-preserving isometries of their supports.
  In particular, it vanishes exactly when those supports are isomorphic.
  Extra points outside the support are invisible to the discrepancy;
  an isometry of the entire underlying spaces follows if both measures
  have full support.

For $\varepsilon>0$ let $\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)$ be the
entropic transport cost of CKMA SYNOPSIS39, item 90. The **debiased
Sinkhorn divergence** is
$$
S_\varepsilon(\mu,\nu)
=\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\mu,\mu)
-\tfrac12\mathop{\mathrm{OT}}_\varepsilon(\nu,\nu).
$$

* **5. Debiased Sinkhorn divergence.** On a compact Euclidean domain
  with quadratic cost, for every $\varepsilon>0$,
  $S_\varepsilon(\mu,\nu)\ge0$, with equality exactly when $\mu=\nu$.
  Moreover $S_\varepsilon(\mu_n,\mu)\to0$ if and only if
  $\mu_n\Rightarrow\mu$. A sufficient general setting is a compact
  metric space with Lipschitz symmetric cost whose Gibbs kernel
  $e^{-c/\varepsilon}$ is positive and universal. These hypotheses
  distinguish the theorem from a claim for arbitrary costs or tails.

### Explicit geometries and empirical inference

* **10. Barycenters on the line.** For $\mu_i\in\mathcal P_2(\mathbb R)$,
  the unique weighted barycenter has quantile function
  $$F_{\bar\mu}^{-1}(u)=\sum_i\lambda_iF_{\mu_i}^{-1}(u).$$
  More generally, for a random measure $\Lambda$ with
  $\mathbb E\int x^2\Lambda(dx)<\infty$, the population barycenter
  has quantile $\mathbb E F_\Lambda^{-1}$ almost everywhere. The quantile
  embedding
  makes this a Hilbert-space mean. Such an averaging formula does not
  hold for arbitrary multivariate transport maps.

* **11. Gaussian transport and barycenters.** For covariance matrices
  $A,B\ge0$,
  $$W_2^2(N(m,A),N(n,B))
  =\|m-n\|^2+\mathop{\mathrm{tr}}
  [A+B-2(A^{1/2}BA^{1/2})^{1/2}].$$
  If $A>0$, the optimal map is
  $x\mapsto n+A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}(x-m)$.
  A barycenter of positive definite Gaussian measures is Gaussian,
  with mean $\sum_i\lambda_i m_i$ and covariance satisfying
  $$\bar A=\sum_i\lambda_i
  (\bar A^{1/2}A_i\bar A^{1/2})^{1/2}.$$
  If the $A_i$ commute, $\bar A=(\sum_i\lambda_i A_i^{1/2})^2$;
  a matrix square-root average is not the general noncommuting solution.

* **12. One-dimensional empirical transport limit.** Suppose $\mu$ is
  supported on $[a,b]$ and has a continuous density bounded above and
  below by positive constants there. Then
  $$nW_2^2(\mu_n,\mu)\Rightarrow
  \int_0^1\frac{B^0(u)^2}{f(F^{-1}(u))^2}\,du,$$
  by the quantile-process delta method. Thus $W_2(\mu_n,\mu)=O_P(n^{-1/2})$
  under these assumptions, faster than the distribution-free bound
  inferred from item 1. Atoms, gaps, and unbounded tails can change
  the rate or invalidate this integral limit.

* **13. Sliced Wasserstein distance.** Let $\sigma$ be uniform probability
  on $S^{d-1}$ and $P_\theta(x)=\theta^\top x$. Then
  $$\mathop{\mathrm{SW}}_p(\mu,\nu)
  =\left(\int W_p^p((P_\theta)_\#\mu,(P_\theta)_\#\nu)
  \,\sigma(d\theta)\right)^{1/p}$$
  defines a metric on $\mathcal P_p(\mathbb R^d)$ and is at most
  $W_p(\mu,\nu)$. Vanishing projected distances imply equality of
  the laws by continuity of characteristic functions and the
  Cramér–Wold characterization. A finite collection of directions alone
  does not determine every multivariate law.

* **18. Consistency of empirical barycenters.** Suppose independent
  identically distributed random measures $\Lambda_i$ are supported in a common compact set
  $K\subset\mathbb R^d$, and the population Fréchet functional
  $\mathbb E W_2^2(\mu,\Lambda_1)$ has a unique minimizer $\bar\mu$.
  Any sequence minimizing $n^{-1}\sum_iW_2^2(\mu,\Lambda_i)$ converges
  almost surely to $\bar\mu$ in $W_2$. Minimizers can be confined to
  the compact convex hull of $K$; uniform convergence there gives the
  argmin conclusion. Noncompact versions require suitable moment and
  compactness control.

<a id="synopsis-111b"></a>

## 111B. Kernel Mean Embeddings and Integral Probability Metrics

Let $\mathcal F$ be a class of real functions. The **integral probability
metric** induced by $\mathcal F$ is
$$\gamma_{\mathcal F}(\mu,\nu)
=\sup_{f\in\mathcal F}\Bigl|\int f\,d\mu-\int f\,d\nu\Bigr|.$$
Let $\mathcal H$ be a separable reproducing-kernel Hilbert space on a
Polish space with a bounded continuous kernel $k$, and let
$\Phi(\mu)=\int k(x,\cdot)\,\mu(dx)$ be the **kernel mean embedding**,
whenever the integral converges in $\mathcal H$. The **maximum mean
discrepancy** is $\mathop{\mathrm{MMD}}(\mu,\nu)=\|\Phi(\mu)-\Phi(\nu)\|_{\mathcal H}$.
The kernel is **characteristic** when $\Phi$ is injective on the space of
Borel probabilities.

* **6. Maximum mean discrepancy.** The discrepancy equals the integral
  probability metric over the unit ball of $\mathcal H$, and
  $$
  \mathop{\mathrm{MMD}}(\mu,\nu)^2
  =\mathbb E k(X,X')+\mathbb E k(Y,Y')-2\mathbb E k(X,Y)
  $$
  for independent copies $X,X'\sim\mu$ and $Y,Y'\sim\nu$. The Gaussian and
  Laplace kernels on $\mathbb R^d$ are characteristic. A continuous
  translation-invariant positive definite kernel on $\mathbb R^d$ is
  characteristic when the support of its spectral measure is all of
  $\mathbb R^d$.

For independent samples of equal size $n\ge2$, use the unbiased estimator
$$\mathop{\mathrm{MMD}}_{u,n}^2
=\frac{\sum_{i\ne j}k(X_i,X_j)+\sum_{i\ne j}k(Y_i,Y_j)}{n(n-1)}
-\frac2{n^2}\sum_{i,j}k(X_i,Y_j).$$
The biased estimator $\mathop{\mathrm{MMD}}_{b,n}^2$ is
$\|\Phi(\mu_n)-\Phi(\nu_n)\|_{\mathcal H}^2$. Let
$(\lambda_j)_{j\ge1}$ be the eigenvalues of the integral operator of the
centered kernel $\tilde k(x,y)=k(x,y)-\mathbb Ek(x,X')-\mathbb Ek(X,y)+\mathbb Ek(X,X')$
on $L^2(\mu)$.

* **7. Limits of the empirical discrepancy.** For the bounded kernel
  above, under $\mu=\nu$,
  $$n\mathop{\mathrm{MMD}}_{u,n}^2\Rightarrow
  2\sum_j\lambda_j(Z_j^2-1),\qquad
  n\mathop{\mathrm{MMD}}_{b,n}^2\Rightarrow2\sum_j\lambda_jZ_j^2.$$
  Here $Z_j$ are independent standard normals and $\lambda_j$ are the
  eigenvalues of the centered one-sample kernel specified above.
  Under a fixed alternative, with $\Delta=\Phi(\mu)-\Phi(\nu)$,
  the $\sqrt n$-normalized centered unbiased statistic has a normal
  limit with variance
  $$4\mathop{\mathrm{Var}}_\mu\langle k(X,\cdot),\Delta\rangle
  +4\mathop{\mathrm{Var}}_\nu\langle k(Y,\cdot),\Delta\rangle.$$
  This variance may be zero, even for a characteristic kernel and unequal
  laws. A nondegenerate normal limit requires it to be positive.

On $\mathbb R^d$, with $X,X'$ independent copies of $\mu$ and $Y,Y'$
independent copies of $\nu$, all four variables independent, the **energy
distance** is
$$
D^2(\mu,\nu)
=2\mathbb E\|X-Y\|-\mathbb E\|X-X'\|-\mathbb E\|Y-Y'\|,
$$
when the first moments are finite. For a pair $(X,Y)$, let $a(x,x')$ be $\|x-x'\|$ centered in both
arguments under the marginal law of $X$, and define $b(y,y')$ similarly.
The squared **distance covariance** is
$\mathcal V^2(X,Y)=\mathbb E[a(X,X')b(Y,Y')]$ for independent copies
of the pair, whenever the expectations exist. Finite second moments are
a sufficient condition. This is not the ordinary Euclidean energy distance
on the concatenated vector space.

* **8. Energy distance and independence.** For laws on $\mathbb R^d$
  with finite first moment, $D^2(\mu,\nu)\ge0$, with equality exactly
  when $\mu=\nu$. For
  $$k_0(x,y)=\tfrac12(\|x\|+\|y\|-\|x-y\|),$$
  one has $D^2(\mu,\nu)=2\mathop{\mathrm{MMD}}_{k_0}(\mu,\nu)^2$.
  Under the stated sufficient moment condition, $\mathcal V^2(X,Y)$
  is nonnegative and vanishes exactly at independence. With these
  distance-induced kernels on the two coordinates,
  $\mathcal V^2(X,Y)=4\mathop{\mathrm{HSIC}}_{k_0,\ell_0}(X,Y)$.
  The factor follows by centering each kernel, which gives $-a/2$
  and $-b/2$, respectively.

Let $k$ and $\ell$ be kernels on the two coordinates of a pair $(X,Y)$, and
let $\mathcal H\otimes\mathcal G$ be the product reproducing-kernel Hilbert
space. The **Hilbert–Schmidt independence criterion** is the
squared Hilbert–Schmidt norm of the cross-covariance operator from
$\mathcal G$ to $\mathcal H$, equivalently the squared maximum mean
discrepancy between the joint law and the product of the marginals for
the product kernel $k\otimes\ell$.

* **9. Hilbert–Schmidt independence criterion.** For bounded continuous
  kernels, assume the product kernel is characteristic on the product
  space, as for Gaussian kernels on Euclidean coordinates. Then HSIC
  vanishes if and only if $X$ and $Y$ are independent. An unbiased
  estimator based on paired observations is a $U$-statistic of order
  four, because both marginal embeddings must also be estimated.
  Under independence its first projection vanishes and its scaled limit
  is a centered weighted chi-squared series. Under alternatives its
  $\sqrt n$ limit is normal, possibly degenerate. The biased Gram-matrix
  estimator in item 17 has an uncentered null limit.

### Kernel estimation, witnesses, and test calibration

* **14. Empirical kernel means.** If $k(x,x)\le\kappa^2$, then
  $$\mathbb E\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}^2
  =\frac1n\left(\mathbb E k(X,X)-\|\Phi(\mu)\|_{\mathcal H}^2\right)
  \le\frac{\kappa^2}{n}.$$
  With probability at least $1-\delta$,
  $$\|\Phi(\mu_n)-\Phi(\mu)\|_{\mathcal H}
  \le\frac\kappa{\sqrt n}
  +\kappa\sqrt{\frac{2\log(1/\delta)}n}.$$
  The second statement follows from bounded differences. The constants
  do not contain the input dimension, although the chosen kernel's
  ability to distinguish the alternatives still matters.

* **15. Witness function.** If $\Delta=\Phi(\mu)-\Phi(\nu)\ne0$, the
  function attaining the MMD supremum is
  $$f^*(x)=\frac{\mathbb E_\mu k(x,X)-\mathbb E_\nu k(x,Y)}
  {\|\Delta\|_{\mathcal H}}.$$
  It has RKHS norm one, and its mean difference is the MMD.
  The unnormalized numerator describes where the distributions differ
  at the resolution selected by the kernel.

* **16. Permutation calibration.** Under equality of two independent
  sample laws, labels are uniform over all allocations of the pooled
  observations to the two fixed sample sizes. Recomputing any fixed
  statistic under those allocations gives a test of conditional level
  at most $\alpha$, or exactly $\alpha$ with boundary randomization.
  This applies to MMD, energy, and empirical transport statistics
  without estimating their asymptotic null laws. For independence
  testing, permuting one coordinate of independent observed pairs
  gives the analogous calibration under the product-law null.

* **17. Gram-matrix independence statistic.** Let $K,L$ be the Gram
  matrices of the two coordinates of $n$ independent pairs and put
  $H=I-11^\top/n$. The biased HSIC estimator is
  $$\widehat{\mathop{\mathrm{HSIC}}}_b=n^{-2}\mathop{\mathrm{tr}}(KHLH).$$
  Under independence its $n$-scaled limit is
  $\sum_{r,s}\lambda_r\eta_sZ_{rs}^2$, where $\lambda_r,\eta_s$
  are eigenvalues of the two centered marginal kernel operators.
  The unbiased order-four estimator has the corresponding centered
  series $\sum_{r,s}\lambda_r\eta_s(Z_{rs}^2-1)$.
  There is one sample of pairs here, unlike the two independent
  samples and factor two in item 7.

## Reference guide

### Correspondence with the subdivisions

- **[111A](#synopsis-111a)**: Villani, Santambrogio, and Ambrosio, Gigli, and
  Savaré carry the analytic theory already numbered in CKMA SYNOPSIS39.
  Peyré and Cuturi carry computational optimal transport and entropic
  regularization. Fournier and Guillin carry empirical Wasserstein rates.
  Agueh and Carlier carry barycenters. Mémoli carries the Gromov–Wasserstein
  distance. Feydy, Séjourné, Vialard, and Peyré carry the debiased Sinkhorn
  divergence.
- **[111B](#synopsis-111b)**: Gretton, Borgwardt, Rasch, Schölkopf, and Smola
  carry the maximum mean discrepancy and its limits. Sejdinovic, Sriperumbudur,
  Gretton, and Fukumizu carry the equivalence of energy distance and a
  kernel discrepancy. Székely, Rizzo, and Bakirov carry distance covariance.
  Gretton, Bousquet, Smola, and Schölkopf carry the Hilbert–Schmidt
  independence criterion.

### Source comparisons and local copies

Panaretos–Zemel is present in `ReferencesSuppl`. Section 1.6.3, the
one-dimensional barycenter theorem in Section 3.2.2, and the Gaussian
covariance equation in Section 5.4.1 were read for items 10 and 11.
Chewi–Niles-Weed–Rigollet is also present there; Chapter 2 develops the
distribution-free empirical bounds and why they need not be sharp for
each law. The quantile-process limit in item 12 specializes SYNOPSIS103,
items 5 and 26, under compact-support density bounds.

For item 1, [Fournier–Guillin, Theorem 1](https://arxiv.org/abs/1312.2128),
was read online. It gives upper bounds with moment remainders, not an
exact rate for every measure. The bounded-domain positivity statement
in item 5 follows [Feydy and coauthors, Theorem 1](https://proceedings.mlr.press/v89/feydy19a.html).
The entropic cost convention is fixed by CKMA SYNOPSIS39, item 90;
debiasing subtracts the two self-costs.

[Gretton and coauthors, Theorem 12](https://www.jmlr.org/papers/v13/gretton12a.html),
was checked for the equal-sample normalization in item 7. Centered
one-sample kernel eigenvalues give the factor two there. The generic
projection argument is SYNOPSIS103, items 27–28. Empirical kernel means,
witnesses, and permutation calibration are the elementary Hilbert-space
and exchangeability consequences recorded in items 14–16.

Energy distance uses a distance-induced kernel with its explicit factor
in item 8. Distance covariance uses products of centered coordinate
distances; the Euclidean energy distance of concatenated pairs is a
different discrepancy. HSIC is the squared norm convention, its unbiased
estimator has order four, and a nonzero discrepancy does not by itself
force a positive first-projection variance. The energy–kernel comparison
is treated by Sejdinovic and coauthors, listed in the bibliography; that
paper was not consulted as a local full text in this expansion.

Local sources and online papers are distinguished here. The local transport
books supply the analytic background; missing local copies of an original
paper were not taken to preclude consulting its primary online version.

Local texts directly consulted or identified for this selection:

- [Panaretos and Zemel, *An Invitation to Statistics in Wasserstein Space*](../lean-CKMA/ReferencesSuppl/PanaretosZemel2020InvitationStatisticsWassersteinSpace-Springer.BriefsPMS.pdf).
  The one-dimensional and Gaussian geometries and barycenter formulas were read.
- [Chewi, Niles-Weed, and Rigollet, *Statistical Optimal Transport*](../lean-CKMA/ReferencesSuppl/ChewiNilesWeedRigollet2025StatisticalOptimalTransportÉcoledÉtéProbabilitésSaintFlourXLIX2019-Springer.LNM2364.pdf).
  Chapter 2 was consulted for empirical measures and dimension-dependent bounds.
- [Peyré and Cuturi, *Computational Optimal Transport*](../lean-CKMA/References/PeyréCuturi2019ComputationalOptimalTransportApplicationsDataSciences-NowPublishers.FnTML11.pdf).
  The entropic problem, Gaussian costs, and sliced transport were consulted;
  the original empirical-rate theorem was checked separately.
- [Villani, *Optimal Transport: Old and New*](../lean-CKMA/References/Villani2009OptimalTransportOldNew-SpringerGL338.pdf).
- [Santambrogio, *Optimal Transport for Applied Mathematicians*](../lean-CKMA/References/Santambrogio2015OptimalTransportAppliedMathematiciansCalculusVariationsPDEsModeling-Birkhäuser.PNDE87.pdf).
- [Ambrosio, Gigli, and Savaré, *Gradient Flows*](../lean-CKMA/References/AmbrosioGigliSavaré2008GradientFlowsMetricSpacesSpaceProbabilityMeasures2ndEd-Birkhäuser.LMETH.pdf).
- [Galichon, *Optimal Transport Methods in Economics*](../lean-CKMA/References/Galichon2016OptimalTransportMethodsEconomics-Princeton.pdf).
