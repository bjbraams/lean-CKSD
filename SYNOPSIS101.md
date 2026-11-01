# Synopsis: Statistical inference: general texts, references, and history

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-101).

This synopsis follows Section 101 of the bibliography. Subdivision 101A is the
shared finite-sample core of a first graduate course in mathematical
statistics. Subdivision 101B collects handbooks and histories; they are used
as sources for formulae and provenance and do not have a separate numbered
list. Decision-theoretic optimality is developed in
[SYNOPSIS102](SYNOPSIS102.md), first-order and higher-order asymptotics in
[SYNOPSIS103](SYNOPSIS103.md), and nonparametric, semiparametric, and robust
procedures in Section 104. Measure-theoretic probability is
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md).

Throughout, a **statistical model** is a family
$\{P_\theta:\theta\in\Theta\}$ of probability measures on a measurable space
$(\mathcal X,\mathcal A)$. The model is **dominated** by a $\sigma$-finite
measure $\mu$ when each $P_\theta$ has a density $f(\cdot\mid\theta)$ with
respect to $\mu$. The **likelihood** of an observation $x$ is the function
$\theta\mapsto L(\theta;x)=f(x\mid\theta)$. The model is **identifiable** when
$\theta\neq\theta'$ implies $P_\theta\neq P_{\theta'}$. A **statistic** is a
measurable map $T$ on $\mathcal X$. An estimator of a function $g(\theta)$ is
a statistic used as a guess of that value; it is **unbiased** when it is
integrable and its expectation equals $g(\theta)$ for every $\theta$.

Samples are independent and identically distributed of size $n$ unless a
statement says otherwise. The sample measure is then the $n$-fold product,
and the sample likelihood is the product of the marginal likelihoods.
Convergence notation and the continuous-mapping and Slutsky theorems are
those of CKMA SYNOPSIS06, items 15 and 16.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-101a"></a>

## 101A. General Graduate Texts

The statements below are the finite-sample results common to the general
graduate texts. Asymptotic expansions of the same procedures are in
Section 103.

### Sufficiency, likelihood, and minimal reduction

For a dominated model on a standard Borel space, a statistic $T$ is
**sufficient** when the regular conditional distribution of the observation
given $T$ can be chosen independent of $\theta$. An **ancillary** statistic
is one whose distribution does not depend on $\theta$.

The **sufficiency principle** says that if $T$ is sufficient and
$T(x)=T(y)$, then $x$ and $y$ yield the same evidence about $\theta$. The
**conditionality principle** says that if an ancillary statistic selects
which of several experiments was performed, then the evidence about $\theta$
is the evidence in the selected experiment. The **likelihood principle**
says that if two outcomes, possibly from different dominated experiments,
have likelihood functions that are positive scalar multiples of one another
as functions of $\theta$, then they yield the same evidence about $\theta$.

* **1. Factorization theorem.** Let the model be dominated by a
  $\sigma$-finite measure $\mu$. A statistic $T$ is sufficient if and only
  if there exist nonnegative measurable functions $g_\theta$ and a
  nonnegative measurable function $h$ such that, for every $\theta$,
  $$f(x\mid\theta)=g_\theta(T(x))\,h(x)$$
  for $\mu$-almost every $x$. In that case the conditional form of
  sufficiency holds whenever a regular conditional distribution exists.

* **2. Minimal sufficiency.** Assume the model is dominated and has a common
  support. Fix a reference parameter $\theta_0$ and write
  $\lambda_\theta(x)=f(x\mid\theta)/f(x\mid\theta_0)$ where the denominator
  is positive. The map $x\mapsto(\lambda_\theta(x))_{\theta\in\Theta}$, taken
  up to $\mu$-null sets, is sufficient, and it is a function of every
  sufficient statistic. Equivalently, a sufficient statistic $T$ is minimal
  when $T(x)=T(y)$ if and only if $\theta\mapsto f(x\mid\theta)$ and
  $\theta\mapsto f(y\mid\theta)$ are positive scalar multiples of one
  another.

* **3. Birnbaum's theorem.** For dominated experiments in the usual discrete
  mixture formulation, the sufficiency principle and the conditionality
  principle together imply the likelihood principle.

### Exponential families

A dominated family is a **natural exponential family** of order $k$ when its
densities can be written
$$f(x\mid\eta)=h(x)\exp\bigl(\eta\cdot T(x)-A(\eta)\bigr),$$
with natural statistic $T$, natural parameter $\eta$, and cumulant function
$A$. The **natural parameter space** is the set $\mathcal N$ of $\eta$ for
which the integral defining $\exp A(\eta)$ is finite. The representation is
**minimal** when the law of $T$ is not supported on a proper affine subspace
and $\mathcal N$ is not contained in a proper affine subspace. The family is
**full rank** when the parameter runs through a set with nonempty interior in
$\mathcal N$ relative to the minimal representation. A **curved** exponential
family is a smooth lower-dimensional subfamily of a full-rank family.

* **4. Structure of a full-rank exponential family.** The natural parameter
  space is convex. On its interior $A$ is real analytic,
  $\nabla A(\eta)=\mathbb E_\eta T$, and
  $\mathop{\mathrm{Hess}} A(\eta)=\mathop{\mathrm{Cov}}_\eta(T)$. In a
  minimal representation the Hessian is positive definite on the interior,
  so the family is identifiable in the mean parameter
  $\nabla A(\eta)$. For an independent sample the sum of the copies of $T$
  is a natural sufficient statistic, and its law is the exponential family
  of the same natural parameter with cumulant function $nA$.

* **5. Completeness in a full-rank exponential family.** In a minimal
  full-rank exponential family, the natural statistic $T$ is complete: a
  measurable function $g$ with $\mathbb E_\eta g(T)=0$ for every natural
  parameter in a nonempty open set satisfies $g(T)=0$ almost surely under
  every such parameter. Bounded completeness is included.

* **6. Pitman–Koopman–Darmois theorem.** Consider independent sampling from
  a dominated family on a Euclidean sample space, with common support, a
  parameter in an open subset of $\mathbb R^k$, and densities positive and
  continuously differentiable in the parameter. Under the classical
  smoothness and constant-rank hypotheses on the densities and the
  sufficient reductions, a sufficient statistic of fixed dimension $d$
  for every sample size implies an exponential-family representation of
  order at most $d$. The reductions here must be regular smooth statistics;
  allowing arbitrary measurable encodings of a sample as a single real
  number would make a dimension assertion meaningless. The common-support hypothesis excludes
  families such as the uniform law on $(0,\theta)$, whose maximum is
  one-dimensional and sufficient for every $n$.

### Unbiased estimation and information

The **Fisher information** of a real parameter, at a point where the model
is dominated, the support does not depend on $\theta$, and the score
$\partial_\theta\log f(X\mid\theta)$ exists and is square-integrable, is
$$I(\theta)=\mathbb E_\theta\bigl(\partial_\theta\log f(X\mid\theta)\bigr)^2.$$
When the second derivative exists and may be passed under the integral,
$I(\theta)=-\mathbb E_\theta\partial_\theta^2\log f(X\mid\theta)$. For a
parameter in an open subset of $\mathbb R^k$ the information matrix is the
covariance of the score vector, and it equals the negative expected Hessian
under the same domination condition. Independent experiments add their
information matrices. An independent sample of size $n$ from a model with
information $I_1(\theta)$ therefore has information $n I_1(\theta)$.

* **7. Rao–Blackwell theorem.** Let $T$ be sufficient and let $\delta$ be an
  estimator with $\mathbb E_\theta|\delta|<\infty$. The conditional
  expectation $\delta^\star(T)=\mathbb E_\theta[\delta\mid T]$ does not
  depend on $\theta$. It has the same expectation as $\delta$. If
  $L(\theta,a)$ is convex in the action $a$, then
  $\mathbb E_\theta L(\theta,\delta^\star(T))\le
  \mathbb E_\theta L(\theta,\delta(X))$.

* **8. Lehmann–Scheffé theorem.** Let $T$ be a complete sufficient statistic
  and let $g(\theta)$ admit an unbiased estimator of finite expectation. There
  is an unbiased estimator of the form $\varphi(T)$, and any two unbiased
  estimators that are functions of $T$ agree almost surely under every
  $P_\theta$. For every loss that is convex in the action, $\varphi(T)$
  minimizes the risk among all unbiased estimators with finite risk.

* **9. Basu's theorem.** Let $T$ be a boundedly complete sufficient statistic
  and let $V$ be ancillary. Then $T$ and $V$ are independent under every
  $P_\theta$.

* **10. Information inequality.** Let $\theta$ lie in an open subset of
  $\mathbb R^k$, and assume the support is free of $\theta$, the information
  matrix $I(\theta)$ exists and is nonsingular, and differentiation under
  the integral is legitimate for the density and for an unbiased estimator
  $W$ of a differentiable map $g$. Then, in the Loewner order,
  $$\mathop{\mathrm{Cov}}_\theta(W)
  \ge Dg(\theta)\,I(\theta)^{-1}\,Dg(\theta)^\top.$$
  For a real parameter and a real unbiased estimator of $g$,
  $\mathop{\mathrm{Var}}_\theta(W)\ge g'(\theta)^2/I(\theta)$.
  For an independent sample the matrix $I(\theta)$ is replaced by
  $n I_1(\theta)$.

* **11. Equality in the information inequality.** Under the hypotheses of
  the one-parameter inequality, assume $g'(\theta)\ne0$ throughout an
  open interval and the usual common-support differentiability conditions.
  Equality holds throughout that interval if and only if the model is a one-parameter exponential family on
  that interval and $g(\theta)$ is an affine function of
  $\mathbb E_\theta T$. The unbiased estimator attaining the bound is then an
  affine function of $T$.

### Minimum-variance unbiased estimators beyond the information bound

An unbiased estimator $W$ of $g(\theta)$ with finite variance under every
$P_\theta$ is **uniformly minimum variance unbiased** (UMVU) when
$\mathop{\mathrm{Var}}_\theta W\le\mathop{\mathrm{Var}}_\theta W'$ for every
$\theta$ and every unbiased estimator $W'$ of $g(\theta)$. An **unbiased
estimator of zero** is a statistic $U$ with $\mathbb E_\theta U=0$ for every
$\theta$. A family $\mathcal P$ of laws on $(\mathcal X,\mathcal A)$ is
**complete** when $\int f\,dP=0$ for every $P\in\mathcal P$ forces $f=0$
$P$-almost everywhere for every $P\in\mathcal P$, the integrals being
assumed to exist.

* **24. Characterization of UMVU estimators.** Let $W$ be an unbiased
  estimator of $g(\theta)$ with $\mathbb E_\theta W^2<\infty$ for every
  $\theta$. Then $W$ is UMVU if and only if
  $\mathop{\mathrm{Cov}}_\theta(W,U)=0$ for every $\theta$ and every unbiased
  estimator $U$ of zero with $\mathbb E_\theta U^2<\infty$ for every
  $\theta$. If $T$ is sufficient and $W=h(T)$, it suffices to check
  unbiased estimators of zero that are functions of $T$. A UMVU estimator
  is unique: two UMVU estimators of $g(\theta)$ agree $P_\theta$-almost
  surely for every $\theta$. The criterion is used chiefly to show that a
  given unbiased estimator is not UMVU, and it applies without
  completeness; with a complete sufficient statistic it reduces to item 8.

* **25. Completeness of the order statistic.** Let $\mathcal P$ be a
  complete family of laws on $(\mathcal X,\mathcal A)$ that is closed under
  finite convex combinations. Then for every $n$ the order statistic, that
  is the $\sigma$-algebra of permutation-invariant events in
  $\mathcal X^n$, is complete for $\{P^n:P\in\mathcal P\}$; it is always
  sufficient. The hypotheses hold for the family of all laws on
  $\mathbb R^d$ with a Lebesgue density, for the family of all laws on
  $\mathbb R$ with continuous distribution function, and for the subfamily
  of laws with a Lebesgue density for which prescribed absolute moments
  are finite. Consequently, if $\kappa(P)=\mathbb E_P h(X_1,\ldots,X_m)$ for a
  symmetric kernel $h$ that is integrable under $P^m$ for every
  $P\in\mathcal P$, and $n\ge m$, the $U$-statistic
  $$U_n=\binom nm^{-1}\sum_{i_1<\cdots<i_m}h(X_{i_1},\ldots,X_{i_m})$$
  is the unique unbiased estimator of $\kappa$ that is symmetric in the
  observations, and it minimizes the risk among all unbiased estimators of
  $\kappa$ for every loss convex in the action. In particular, among laws
  with a Lebesgue density, $\bar X$ is UMVU for the mean when the variance is
  finite, and $S^2$ is UMVU for the variance when the fourth moment is
  finite. Convex closure cannot be dropped: for $n\ge2$ and the normal
  location family $N(\mu,1)$ the nonzero function
  $n\bar X^2-\sum_i X_i^2+n-1$ is symmetric with expectation zero for every
  $\mu$. The large-sample behaviour of $U_n$ is SYNOPSIS103, item 6.

### Tests and confidence sets

A **test** is a measurable function $\varphi$ with values in $[0,1]$; the
value is the probability of rejecting the null hypothesis after seeing the
observation. The **size** at a null point is $\mathbb E\varphi$, and the
**power** at an alternative is the same expectation. A test of
$H:\theta\in\Theta_0$ against $K:\theta\in\Theta_1$ is **uniformly most
powerful** of its size when, among all tests whose size on $\Theta_0$ is at
most $\alpha$, it maximizes the power at every point of $\Theta_1$. The
family has **monotone likelihood ratio** in a real statistic $T$ when, for
$\theta_2>\theta_1$, the ratio $f(\cdot\mid\theta_2)/f(\cdot\mid\theta_1)$ is
a nondecreasing function of $T$.

A family of tests of the hypotheses $H_0:\theta'=\theta$, one test for each
candidate value $\theta$, determines the **confidence set**
$C(x)=\{\theta:\text{the test of }\theta\text{ accepts }x\}$.

* **12. Neyman–Pearson lemma.** Let $P_0$ and $P_1$ be dominated by $\mu$,
  with densities $f_0$ and $f_1$, and fix $\alpha\in(0,1)$. There exist
  $k\ge 0$ and a test $\varphi$ with $\mathbb E_{P_0}\varphi=\alpha$ such
  that $\varphi=1$ when $f_1>k f_0$ and $\varphi=0$ when $f_1<k f_0$. Any
  such test is most powerful of level $\alpha$ for $P_0$ against $P_1$.
  Every most powerful level-$\alpha$ test agrees with $\varphi$ almost
  everywhere under $P_0+P_1$, except possibly on $\{f_1=k f_0\}$.

* **13. Karlin–Rubin theorem.** Suppose the family has monotone likelihood
  ratio in a real statistic $T$. For $\theta_0\in\Theta$ and $\alpha\in(0,1)$,
  any test that rejects for large values of $T$, and that has size $\alpha$
  at $\theta_0$, is uniformly most powerful of level $\alpha$ for
  $H:\theta\le\theta_0$ against $K:\theta>\theta_0$. Its power function is
  nondecreasing. A one-parameter exponential family has monotone likelihood
  ratio in its natural statistic, so the one-sided test based on that
  statistic is uniformly most powerful.

* **14. Tests and confidence sets.** If, for each $\theta$, $\varphi_\theta$ is
  a nonrandomized test of size $\alpha$ for the hypothesis that the
  parameter equals $\theta$, and $C(x)$ is the set of $\theta$ accepted by
  $\varphi_\theta$, then $P_\theta(\theta\in C(X))=1-\alpha$. Conversely,
  the acceptance events of a confidence set of coverage $1-\alpha$ are tests
  of size $\alpha$. If the tests are uniformly most powerful for the
  one-sided hypotheses, the resulting one-sided confidence bound is
  **uniformly most accurate**: for every $\theta'<\theta$, the probability
  under $P_\theta$ of covering $\theta'$ is minimal among all level-$(1-\alpha)$
  lower bounds.

* **15. Gaussian sampling distributions.** Let $X_1,\ldots,X_n$ be
  independent $N(\mu,\sigma^2)$ random variables with $\sigma>0$, and write
  $\bar X=n^{-1}\sum_i X_i$ and
  $S^2=(n-1)^{-1}\sum_i(X_i-\bar X)^2$. Then $\bar X$ is
  $N(\mu,\sigma^2/n)$, $(n-1)S^2/\sigma^2$ is $\chi^2_{n-1}$, and $\bar X$
  and $S^2$ are independent. Hence
  $\sqrt n\,(\bar X-\mu)/S$ has the Student $t$ law on $n-1$ degrees of
  freedom, and
  $$\bar X\pm t_{n-1,1-\alpha/2}\,S/\sqrt n$$
  is a confidence interval for $\mu$ of exact coverage $1-\alpha$. If $\mu$
  is known, $\sum_i(X_i-\mu)^2/\sigma^2$ is $\chi^2_n$. For two independent
  normal samples, the ratio $(S_1^2/\sigma_1^2)/(S_2^2/\sigma_2^2)$
  has an $F$ law whose degrees of freedom are the two sample sizes minus
  one. In particular, $S_1^2/S_2^2$ has that law when the population
  variances agree. The sample sizes in these variance statements are at
  least two.

* **16. Invariance of maximum likelihood.** Let $\hat\theta(x)$ maximize
  $\theta\mapsto L(\theta;x)$. For a map $g$ on the parameter space, the
  induced likelihood of a value $\psi$ is the supremum of $L(\theta;x)$ over
  $\{\theta:g(\theta)=\psi\}$. Then $g(\hat\theta(x))$ maximizes the induced
  likelihood.

### Likelihood ratio tests and two-sample normal procedures

For a hypothesis $H:\theta\in\Theta_0$ with alternative
$\theta\in\Theta\setminus\Theta_0$, the **likelihood ratio statistic** is
$$\lambda(x)=\frac{\sup_{\theta\in\Theta_0}L(\theta;x)}
{\sup_{\theta\in\Theta}L(\theta;x)}\in[0,1],$$
and a **likelihood ratio test** rejects when $\lambda(x)\le c$ for a
constant $c\in[0,1]$, chosen to give the desired size. Its large-sample
calibration is SYNOPSIS103, item 7; the statements below are exact.

* **26. Likelihood ratio tests in finite samples.** If $T$ is sufficient
  then $\lambda(x)$ depends on $x$ only through $T(x)$. For a sample from
  $N(\theta,1)$ and $H:\theta=\theta_0$,
  $\lambda=\exp(-n(\bar X-\theta_0)^2/2)$, so the test rejects for large
  $|\bar X-\theta_0|$ and has exact size from the normal law of $\bar X$.
  For a sample from $N(\mu,\sigma^2)$ with both parameters unknown,
  $n\ge2$, and $H:\mu=\mu_0$, the restricted and unrestricted maximizers give
  $$\lambda^{-2/n}=1+\frac{t^2}{n-1},\qquad
  t=\frac{\sqrt n(\bar X-\mu_0)}{S},$$
  so the likelihood ratio test is the two-sided Student $t$ test of item 15.
  For $H:\mu\le\mu_0$ the likelihood ratio test is the one-sided $t$ test.

* **27. Two-sample $t$ procedures.** Let $X_1,\ldots,X_m$ be independent
  $N(\mu_X,\sigma^2)$ and $Y_1,\ldots,Y_n$ independent $N(\mu_Y,\sigma^2)$,
  the two samples independent with a common unknown variance, and
  $m+n\ge3$. With the pooled variance
  $$S_p^2=\frac{\sum_i(X_i-\bar X)^2+\sum_j(Y_j-\bar Y)^2}{m+n-2},$$
  the statistic
  $$\frac{\bar X-\bar Y-(\mu_X-\mu_Y)}{S_p\sqrt{1/m+1/n}}$$
  has the Student $t$ law on $m+n-2$ degrees of freedom. It yields an exact
  confidence interval for $\mu_X-\mu_Y$ and exact one- and two-sided tests
  of $\mu_X=\mu_Y$; these tests are uniformly most powerful unbiased and
  uniformly most powerful invariant, see SYNOPSIS102, items 13 and 38.
  Without equality of the variances the statistic with separate variance
  estimates is not a pivot; this is the Behrens–Fisher problem.

### Order statistics and exact confidence procedures

Write $X_{(1)}\le\cdots\le X_{(n)}$ for the **order statistics** of a real
sample. A **pivot** is a function of the observations and the parameter
whose distribution is independent of the parameter. A **$p$-value** for a
null family is a statistic $p(X)\in[0,1]$ such that
$P_\theta(p(X)\le u)\le u$ for every $u\in[0,1]$ and every null parameter.

* **17. Distribution of order statistics.** For independent observations
  with continuous distribution function $F$ and density $f$, the joint
  density of the order statistics is $n!\prod_i f(x_i)$ on
  $x_1<\cdots<x_n$. The density of $X_{(j)}$ is
  $$\frac{n!}{(j-1)!(n-j)!}F(x)^{j-1}(1-F(x))^{n-j}f(x).$$
  In particular, $F(X_{(j)})$ has the
  $\mathop{\mathrm{Beta}}(j,n+1-j)$ law. The ranks of the original
  observations are uniform on the $n!$ permutations and independent of the
  ordered sample. This is the finite-sample basis of the rank methods in
  [SYNOPSIS104](SYNOPSIS104.md), items 2 and 23.

* **18. Quantile confidence intervals.** Suppose $F$ is continuous and
  $F(q_p)=p\in(0,1)$. For $1\le r<s\le n$,
  $$P(X_{(r)}\le q_p\le X_{(s)})
  =\sum_{j=r}^{s-1}\binom nj p^j(1-p)^{n-j}.$$
  Thus binomial quantiles yield confidence intervals for a population
  quantile with coverage independent of $F$. Taking $X_{(0)}=-\infty$
  and $X_{(n+1)}=\infty$ extends the construction to extreme confidence
  levels. Quantile asymptotics are SYNOPSIS103, item 5.

* **19. Exact binomial confidence interval.** If $S\sim
  \mathop{\mathrm{Bin}}(n,p)$, the Clopper–Pearson interval has endpoints
  $$L(s)=B_{s,n-s+1}^{-1}(\alpha/2),\qquad
  U(s)=B_{s+1,n-s}^{-1}(1-\alpha/2),$$
  with $L(0)=0$ and $U(n)=1$; $B_{a,b}^{-1}$ denotes a beta quantile.
  For every $p\in[0,1]$, $P_p(L(S)\le p\le U(S))\ge1-\alpha$.
  Discreteness generally makes the coverage larger than the nominal level.

* **20. Fisher's exact test.** Let $S_1,S_2$ be independent binomial counts
  with sample sizes $n_1,n_2$. Under equality of their success probabilities,
  conditionally on $S_1+S_2=s$,
  $$P(S_1=j\mid S_1+S_2=s)
  =\frac{\binom{n_1}j\binom{n_2}{s-j}}{\binom{n_1+n_2}s}.$$
  This law is free of the common probability. Its upper tail gives a valid
  conditional and unconditional $p$-value for a larger success probability
  in the first population. Randomization at the critical count gives exact
  conditional size when desired.

* **21. Tail probabilities as $p$-values.** For a real statistic $T$, the
  upper-tail probability $P_0(T\ge T(x))$ is a valid $p$-value for a simple
  null. It is uniform on $[0,1]$ if the null law of $T$ is continuous.
  For a composite null,
  $p(x)=\sup_{\theta\in\Theta_0}P_\theta(T\ge T(x))$ is valid whenever
  it is measurable. Conditioning on a statistic whose conditional null
  distribution of $T$ is parameter-free gives the same validity by
  averaging the conditional error bounds.

* **22. Exact inference for normal variance.** Under the normal sampling
  assumptions of item 15, with $n\ge2$, a confidence interval for $\sigma^2$
  of exact coverage $1-\alpha$ is
  $$\left[\frac{(n-1)S^2}{\chi^2_{n-1,1-\alpha/2}},
  \frac{(n-1)S^2}{\chi^2_{n-1,\alpha/2}}\right].$$
  For two independent samples, division of the observed variance ratio by
  the corresponding $F$ quantiles gives an exact interval for the ratio of
  population variances. The degrees of freedom are the two sample sizes
  minus one; equality of the population variances is needed for a test of
  ratio one, rather than for the pivot itself.

* **23. Bias–variance and prediction decompositions.** For a
  square-integrable vector estimator $T$ of $g(\theta)$,
  $$\mathbb E_\theta\|T-g(\theta)\|^2
  =\|\mathbb E_\theta T-g(\theta)\|^2
  +\mathop{\mathrm{tr}}\mathop{\mathrm{Cov}}_\theta(T).$$
  If $m(X)=\mathbb E[Y\mid X]$ and $Y\in L^2$, then for every
  square-integrable predictor $a(X)$,
  $$\mathbb E(Y-a(X))^2
  =\mathbb E\mathop{\mathrm{Var}}(Y\mid X)
  +\mathbb E(m(X)-a(X))^2.$$
  Thus conditional expectation minimizes squared prediction risk. For a
  predictor fitted on independent training data the same identity holds
  conditionally on that data.

### Pivots, interval length, and conditional inference

A **location–scale family** on $\mathbb R$ has densities
$\sigma^{-1}f((x-\mu)/\sigma)$ with $f$ a known density, $\mu\in\mathbb R$,
and $\sigma>0$; the **location** and **scale** families fix $\sigma=1$ and
$\mu=0$ respectively. A statistic $T$ on samples of size $n$ is
**location equivariant** when $T(x+c\mathbf 1)=T(x)+c$, and a positive
statistic $S$ is **scale equivariant** when $S(ax+b\mathbf 1)=aS(x)$ for
$a>0$ and $b\in\mathbb R$; here $\mathbf 1$ is the vector of ones. A
statistic is location–scale equivariant when
$T(ax+b\mathbf 1)=aT(x)+b$.

* **28. Pivots in location and scale families.** For an independent sample
  from a location–scale family, let $T$ be location–scale equivariant and
  $S$ scale equivariant and positive. Then $(T-\mu)/S$ and $S/\sigma$ are
  pivots, and so is $T-\mu$ when $\sigma$ is known. If $a<b$ are quantiles
  with $P(a\le (T-\mu)/S\le b)=1-\alpha$, then $[T-bS,\,T-aS]$ is a
  confidence interval for $\mu$ of exact coverage $1-\alpha$. Examples: for
  an exponential sample with mean $\lambda$, $2\sum_iX_i/\lambda$ is
  $\chi^2_{2n}$; for a sample from the uniform law on $(0,\theta)$,
  $X_{(n)}/\theta$ has distribution function $t^n$ on $[0,1]$, so
  $[X_{(n)},\,\alpha^{-1/n}X_{(n)}]$ covers $\theta$ with probability exactly
  $1-\alpha$. The normal pivots of items 15 and 22 are the Gaussian case.

* **29. Shortest intervals from a unimodal pivot.** Let a pivot have a
  density $f$ that is unimodal with mode $x^\ast$. If $[a,b]$ satisfies
  $\int_a^bf=1-\alpha$, $f(a)=f(b)>0$, and $a\le x^\ast\le b$, then $[a,b]$ has
  minimal length among all intervals of probability $1-\alpha$ under $f$.
  For a location pivot $T-\mu$ this gives the shortest interval of the form
  $[T-b,T-a]$, and for a symmetric unimodal pivot the equal-tailed choice.
  For scale pivots the length of the resulting interval for the parameter
  is not $b-a$, and the criterion must be applied to the transformed
  length.

* **30. Pratt's theorem.** Let $C(x)\subset\mathbb R^k$ be a confidence set
  for $\theta\in\mathbb R^k$ such that $\{(x,\theta):\theta\in C(x)\}$ is
  jointly measurable, and let $|C(x)|$ be its Lebesgue measure. Then, for
  every $\theta^\ast$,
  $$\mathbb E_{\theta^\ast}|C(X)|
  =\int_{\theta\ne\theta^\ast}P_{\theta^\ast}(\theta\in C(X))\,d\theta.$$
  Expected length or volume is thus the integrated probability of false
  coverage. A confidence set minimizing every false-coverage probability
  within a class therefore minimizes expected volume within that class;
  see item 14 and SYNOPSIS102, item 34.

* **31. Conditional inference in a location family.** Let
  $X_1,\ldots,X_n$ be independent with density $f(x-\theta)$ on
  $\mathbb R$, and let $T$ be a location-equivariant statistic, for example
  $X_{(1)}$ or an equivariant maximum likelihood estimator. The
  **configuration**
  $A=(X_1-T,\ldots,X_n-T)$ is ancillary, and it is a maximal invariant
  under translation. Given $A=a$, the conditional density of $T$ is
  $$t\mapsto\frac{\prod_{i=1}^nf(a_i+t-\theta)}
  {\int\prod_{i=1}^nf(a_i+u-\theta)\,du},$$
  that is, the likelihood normalized as a function of the location. The
  conditional law of $T-\theta$ given $A$ is free of $\theta$, so its
  conditional quantiles give confidence sets with conditional coverage
  $1-\alpha$ given almost every configuration, hence also unconditionally. This is Fisher's conditional inference, the case of
  the conditionality principle in which the ancillary is the configuration.
  The minimum-risk equivariant estimator is computed from the same
  conditional law; see SYNOPSIS102, item 8.

<a id="synopsis-101b"></a>

## 101B. Large References, Distribution Handbooks, and History

Johnson, Kotz, and Balakrishnan, and Kendall's *Advanced Theory*, record
densities, moments, and relations among the classical families used in the
statements above. Stigler, Hald, and Lehmann's historical essay record the
provenance of sufficiency, likelihood, least squares, and the Neyman–Pearson
theory. Those sources do not add a further numbered list in this selection.

## Reference guide

### Correspondence with the subdivisions

- **[101A](#synopsis-101a)**: Casella–Berger, Schervish, Cox–Hinkley,
  Bickel–Doksum, Borovkov, Cramér, and Pfanzagl develop the factorization
  theorem, exponential families, completeness, the information inequality,
  the Neyman–Pearson and Karlin–Rubin theorems, and the normal sampling
  laws.
- **[101B](#synopsis-101b)**: The distribution catalogues and the histories
  support formulae and attribution. They are not given numbered entries in
  this pass.

### Source comparisons and local copies

The expanded sampling and exact-inference group uses Casella–Berger,
Section 5.4 (Theorems 5.4.4 and 5.4.6 and the uniform-order-statistic
example), Section 8.3.4 (validity of tail and conditional $p$-values and
Example 8.3.30), and Section 9.2 with Exercise 9.21 (exact binomial
intervals). These passages were read in the local copy. The quantile
confidence formula follows by counting observations below the quantile;
the variance interval uses the pivot in item 15. Item 23 records the
squared-error consequences of conditional projection, rather than
introducing a separate probability theorem.

The third expansion (items 24–31) uses Casella–Berger, Theorems 7.3.19
and 7.3.20 and Example 7.3.21 (unbiased estimators of zero), Definition
8.2.1, Theorem 8.2.4, and Examples 8.2.2, 8.2.6 and Exercise 8.41 (likelihood
ratio tests and the two-sample $t$ test), Definition 9.2.6 and Examples
9.2.7 and 9.2.8 (location–scale and gamma pivots), and Theorems 9.3.2 and
9.3.9 (shortest unimodal intervals and Pratt's theorem). Pratt's theorem is
stated in the Fubini form of Young–Smith, Section 7.3, rather than with the
monotone endpoints of Casella–Berger. Shao's exercise volume records the
UMVU criterion and the Watson–Royall completeness of order statistics as
Theorems 3.2 and 3.13 of his main text. Item 25 follows Pfanzagl,
Section 1.5 (Definition 1.5.4, Theorem 1.5.10, Corollary 1.5.11, and the
normal counterexample after Theorem 1.5.10) and Theorem 3.2.7; Cox–Hinkley,
Section 6.2, uses the same completeness for permutation tests. Item 31 is
Cox–Hinkley, Example 4.15 and Example 2.36, with Young–Smith, Sections 5.2
and 9.8 (the configuration as maximal invariant and ancillary), and Berger,
Section 6.5, Example 16.

The same finite-sample core is shared by the general texts of subdivision
101A. Casella–Berger, Chapters 3 and 5–9, is the detailed first-course
development: exponential families, sufficiency, unbiased estimation,
hypothesis tests, and confidence sets. Schervish, Chapters 2, 4, and 5,
gives the measure-theoretic forms of sufficiency, testing, and estimation.
Cox–Hinkley, Chapters 2, 4, 5, 7, and 8, organizes the same results by the
sufficiency, conditionality, and likelihood principles. Borovkov,
Chapter II, treats sufficiency, completeness, exponential families, and the
information inequality in the Russian course tradition. Cramér,
Chapters 27–35, is the classical source for sampling distributions, the
information inequality, and confidence regions. Pfanzagl, Chapters 1–5,
records minimal sufficiency, completeness, the Rao–Blackwell and
Lehmann–Scheffé theorems, the Neyman–Pearson lemma, monotone likelihood
ratio, and the duality of tests and confidence bounds. Bickel–Doksum,
Volume I, Chapters 1–4, carries the same course at a higher level of
mathematical detail.

Birnbaum's theorem is the form in Casella–Berger, Chapter 6, and
Cox–Hinkley, Chapter 2. The Pitman–Koopman–Darmois theorem is the
common-support form discussed with Brown's exponential-family monograph.
Equality cases of the information inequality are in Cramér and in
Pfanzagl, Chapter 2.

Lehmann and Casella, *Theory of Point Estimation*, and Lehmann and Romano,
*Testing Statistical Hypotheses*, are the standard research monographs for
this material and for Section 102. They are not in the local reference
directory. Shao's *Mathematical Statistics* and Keener's *Theoretical
Statistics* are likewise absent locally; Shao's companion exercise volume is
present and cites the theorem numbers of the main text. The numbered statements were
matched to the local texts listed below.

Local texts directly consulted for this selection:

- [Casella and Berger, *Statistical Inference*](../lean-CKMA/References/CasellaBerger2024StatisticalInference2ndEd-ChapmanHallCRC.TextsStatSci.pdf).
- [Schervish, *Theory of Statistics*](../lean-CKMA/References/Schervish1995TheoryStatistics-Springer.SSS.pdf).
- [Cox and Hinkley, *Theoretical Statistics*](../lean-CKMA/References/CoxHinkley1974TheoreticalStatistics-ChapmanHallCRC.pdf).
- [Bickel and Doksum, *Mathematical Statistics*, Volume I](../lean-CKMA/References/BickelDoksum2015MathematicalStatisticsBasicIdeasSelectedTopics2ndEdVol1-ChapmanHallCRC.TextsStatSci.pdf).
- [Borovkov, *Mathematical Statistics*](../lean-CKMA/References/Borovkov1998MathematicalStatistics-GordonBreach.pdf).
- [Cramér, *Mathematical Methods of Statistics*](../lean-CKMA/References/Cramér1946MathematicalMethodsStatistics-Princeton.MathSer9.pdf).
- [Pfanzagl, *Parametric Statistical Theory*](../lean-CKMA/References/Pfanzagl1994ParametricStatisticalTheory-DeGruyter.Textbook.pdf).
- [Brown, *Fundamentals of Statistical Exponential Families*](../lean-CKMA/References/Brown1986FundamentalsStatisticalExponentialFamiliesApplicationsStatisticalDecisionTheory-IMS.LNMS9.pdf).
- [Young and Smith, *Essentials of Statistical Inference*](../lean-CKMA/References/YoungSmith2005EssentialsStatisticalInference-Cambridge.SerStatProbMath.pdf).
- [Shao, *Mathematical Statistics: Exercises and Solutions*](../lean-CKMA/References/Shao2005MathematicalStatisticsExercisesSolutions-Springer.pdf).
- [Berger, *Statistical Decision Theory and Bayesian Analysis*](../lean-CKMA/References/Berger1985StatisticalDecisionTheoryBayesianAnalysis2ndEd-Springer.SSS.pdf).
