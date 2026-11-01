# Synopsis: Statistical inference: foundations, decision theory, estimation, and testing

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-101).

This synopsis follows Section 101 of the bibliography. It is the finite-sample
core of mathematical statistics: sufficiency and likelihood, exponential
families, unbiased estimation and information, tests and confidence sets,
exact sampling procedures, and the decision theory of minimaxity,
admissibility, equivariance, unbiased and invariant tests, comparison of
experiments, and simultaneous inference. Bibliography subdivision
[101A](CKSD-bib.md#cks-101a) holds the general texts and the
decision-theoretic monographs; [101B](CKSD-bib.md#cks-101b) holds handbooks
and histories, which support formulae and attribution without numbered
entries. Asymptotic theory is [SYNOPSIS102](SYNOPSIS102.md), nonparametric
and high-dimensional inference [SYNOPSIS103](SYNOPSIS103.md), Bayesian
theory beyond the Bayes rules used here [SYNOPSIS104](SYNOPSIS104.md), and
the normal linear model [SYNOPSIS105](SYNOPSIS105.md). Large-scale multiple
testing is in subdivision 103B. Measure-theoretic probability is
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md).

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

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

The statements below are the finite-sample results common to the general
graduate texts. Asymptotic expansions of the same procedures are in
Section 102.

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

* **12. Characterization of UMVU estimators.** Let $W$ be an unbiased
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

* **13. Completeness of the order statistic.** Let $\mathcal P$ be a
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
  $\mu$. The large-sample behaviour of $U_n$ is SYNOPSIS102, item 8.

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

* **14. Neyman–Pearson lemma.** Let $P_0$ and $P_1$ be dominated by $\mu$,
  with densities $f_0$ and $f_1$, and fix $\alpha\in(0,1)$. There exist
  $k\ge 0$ and a test $\varphi$ with $\mathbb E_{P_0}\varphi=\alpha$ such
  that $\varphi=1$ when $f_1>k f_0$ and $\varphi=0$ when $f_1<k f_0$. Any
  such test is most powerful of level $\alpha$ for $P_0$ against $P_1$.
  Every most powerful level-$\alpha$ test agrees with $\varphi$ almost
  everywhere under $P_0+P_1$, except possibly on $\{f_1=k f_0\}$.

* **15. Karlin–Rubin theorem.** Suppose the family has monotone likelihood
  ratio in a real statistic $T$. For $\theta_0\in\Theta$ and $\alpha\in(0,1)$,
  any test that rejects for large values of $T$, and that has size $\alpha$
  at $\theta_0$, is uniformly most powerful of level $\alpha$ for
  $H:\theta\le\theta_0$ against $K:\theta>\theta_0$. Its power function is
  nondecreasing. A one-parameter exponential family has monotone likelihood
  ratio in its natural statistic, so the one-sided test based on that
  statistic is uniformly most powerful.

* **16. Tests and confidence sets.** If, for each $\theta$, $\varphi_\theta$ is
  a nonrandomized test of size $\alpha$ for the hypothesis that the
  parameter equals $\theta$, and $C(x)$ is the set of $\theta$ accepted by
  $\varphi_\theta$, then $P_\theta(\theta\in C(X))=1-\alpha$. Conversely,
  the acceptance events of a confidence set of coverage $1-\alpha$ are tests
  of size $\alpha$. If the tests are uniformly most powerful for the
  one-sided hypotheses, the resulting one-sided confidence bound is
  **uniformly most accurate**: for every $\theta'<\theta$, the probability
  under $P_\theta$ of covering $\theta'$ is minimal among all level-$(1-\alpha)$
  lower bounds.

* **17. Gaussian sampling distributions.** Let $X_1,\ldots,X_n$ be
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

* **18. Invariance of maximum likelihood.** Let $\hat\theta(x)$ maximize
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
calibration is SYNOPSIS102, item 11; the statements below are exact.

* **19. Likelihood ratio tests in finite samples.** If $T$ is sufficient
  then $\lambda(x)$ depends on $x$ only through $T(x)$. For a sample from
  $N(\theta,1)$ and $H:\theta=\theta_0$,
  $\lambda=\exp(-n(\bar X-\theta_0)^2/2)$, so the test rejects for large
  $|\bar X-\theta_0|$ and has exact size from the normal law of $\bar X$.
  For a sample from $N(\mu,\sigma^2)$ with both parameters unknown,
  $n\ge2$, and $H:\mu=\mu_0$, the restricted and unrestricted maximizers give
  $$\lambda^{-2/n}=1+\frac{t^2}{n-1},\qquad
  t=\frac{\sqrt n(\bar X-\mu_0)}{S},$$
  so the likelihood ratio test is the two-sided Student $t$ test of item 17.
  For $H:\mu\le\mu_0$ the likelihood ratio test is the one-sided $t$ test.

* **20. Two-sample $t$ procedures.** Let $X_1,\ldots,X_m$ be independent
  $N(\mu_X,\sigma^2)$ and $Y_1,\ldots,Y_n$ independent $N(\mu_Y,\sigma^2)$,
  the two samples independent with a common unknown variance, and
  $m+n\ge3$. With the pooled variance
  $$S_p^2=\frac{\sum_i(X_i-\bar X)^2+\sum_j(Y_j-\bar Y)^2}{m+n-2},$$
  the statistic
  $$\frac{\bar X-\bar Y-(\mu_X-\mu_Y)}{S_p\sqrt{1/m+1/n}}$$
  has the Student $t$ law on $m+n-2$ degrees of freedom. It yields an exact
  confidence interval for $\mu_X-\mu_Y$ and exact one- and two-sided tests
  of $\mu_X=\mu_Y$; these tests are uniformly most powerful unbiased and
  uniformly most powerful invariant, see items 46 and 56.
  Without equality of the variances the statistic with separate variance
  estimates is not a pivot; this is the Behrens–Fisher problem.

### Order statistics and exact confidence procedures

Write $X_{(1)}\le\cdots\le X_{(n)}$ for the **order statistics** of a real
sample. A **pivot** is a function of the observations and the parameter
whose distribution is independent of the parameter. A **$p$-value** for a
null family is a statistic $p(X)\in[0,1]$ such that
$P_\theta(p(X)\le u)\le u$ for every $u\in[0,1]$ and every null parameter.

* **21. Distribution of order statistics.** For independent observations
  with continuous distribution function $F$ and density $f$, the joint
  density of the order statistics is $n!\prod_i f(x_i)$ on
  $x_1<\cdots<x_n$. The density of $X_{(j)}$ is
  $$\frac{n!}{(j-1)!(n-j)!}F(x)^{j-1}(1-F(x))^{n-j}f(x).$$
  In particular, $F(X_{(j)})$ has the
  $\mathop{\mathrm{Beta}}(j,n+1-j)$ law. The ranks of the original
  observations are uniform on the $n!$ permutations and independent of the
  ordered sample. This is the finite-sample basis of the rank methods in
  [SYNOPSIS103](SYNOPSIS103.md), items 2 and 19.

* **22. Quantile confidence intervals.** Suppose $F$ is continuous and
  $F(q_p)=p\in(0,1)$. For $1\le r<s\le n$,
  $$P(X_{(r)}\le q_p\le X_{(s)})
  =\sum_{j=r}^{s-1}\binom nj p^j(1-p)^{n-j}.$$
  Thus binomial quantiles yield confidence intervals for a population
  quantile with coverage independent of $F$. Taking $X_{(0)}=-\infty$
  and $X_{(n+1)}=\infty$ extends the construction to extreme confidence
  levels. Quantile asymptotics are SYNOPSIS102, item 6.

* **23. Exact binomial confidence interval.** If $S\sim
  \mathop{\mathrm{Bin}}(n,p)$, the Clopper–Pearson interval has endpoints
  $$L(s)=B_{s,n-s+1}^{-1}(\alpha/2),\qquad
  U(s)=B_{s+1,n-s}^{-1}(1-\alpha/2),$$
  with $L(0)=0$ and $U(n)=1$; $B_{a,b}^{-1}$ denotes a beta quantile.
  For every $p\in[0,1]$, $P_p(L(S)\le p\le U(S))\ge1-\alpha$.
  Discreteness generally makes the coverage larger than the nominal level.

* **24. Fisher's exact test.** Let $S_1,S_2$ be independent binomial counts
  with sample sizes $n_1,n_2$. Under equality of their success probabilities,
  conditionally on $S_1+S_2=s$,
  $$P(S_1=j\mid S_1+S_2=s)
  =\frac{\binom{n_1}j\binom{n_2}{s-j}}{\binom{n_1+n_2}s}.$$
  This law is free of the common probability. Its upper tail gives a valid
  conditional and unconditional $p$-value for a larger success probability
  in the first population. Randomization at the critical count gives exact
  conditional size when desired.

* **25. Tail probabilities as $p$-values.** For a real statistic $T$, the
  upper-tail probability $P_0(T\ge T(x))$ is a valid $p$-value for a simple
  null. It is uniform on $[0,1]$ if the null law of $T$ is continuous.
  For a composite null,
  $p(x)=\sup_{\theta\in\Theta_0}P_\theta(T\ge T(x))$ is valid whenever
  it is measurable. Conditioning on a statistic whose conditional null
  distribution of $T$ is parameter-free gives the same validity by
  averaging the conditional error bounds.

* **26. Exact inference for normal variance.** Under the normal sampling
  assumptions of item 17, with $n\ge2$, a confidence interval for $\sigma^2$
  of exact coverage $1-\alpha$ is
  $$\left[\frac{(n-1)S^2}{\chi^2_{n-1,1-\alpha/2}},
  \frac{(n-1)S^2}{\chi^2_{n-1,\alpha/2}}\right].$$
  For two independent samples, division of the observed variance ratio by
  the corresponding $F$ quantiles gives an exact interval for the ratio of
  population variances. The degrees of freedom are the two sample sizes
  minus one; equality of the population variances is needed for a test of
  ratio one, rather than for the pivot itself.

* **27. Bias–variance and prediction decompositions.** For a
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
  $1-\alpha$. The normal pivots of items 17 and 26 are the Gaussian case.

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
  see item 16 and item 52.

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
  conditional law; see item 40.

### Finite decision problems

A **decision problem** consists of the model
$\{P_\theta:\theta\in\Theta\}$, an action space $\mathcal A$, and a loss
$L(\theta,a)$. A **randomized decision rule** is a Markov kernel from the
sample space to $\mathcal A$. Its **risk** is
$R(\theta,\delta)=\mathbb E_\theta L(\theta,\delta(X))$. A rule is
**admissible** when no other rule has risk less than or equal to its risk
for every $\theta$ and strictly smaller risk for some $\theta$. It is
**minimax** when it minimizes $\sup_\theta R(\theta,\delta)$. A probability
$\pi$ on $\Theta$ is a **prior**. The **Bayes risk** of a rule is
$r(\pi,\delta)=\int R(\theta,\delta)\,\pi(d\theta)$, and a **Bayes rule**
minimizes the Bayes risk. A rule is **extended Bayes** when its Bayes risk
comes arbitrarily close to the minimal Bayes risk along some sequence of
priors.

* **32. Value of a finite statistical game.** If $\Theta$ and $\mathcal A$
  are finite, the statistical game has a value: the minimax risk equals
  the supremum over priors of the minimal Bayes risk. A minimax rule exists,
  and a least favorable prior exists. Priors are mixed strategies for
  nature, and randomized rules are mixed strategies for the statistician.

* **33. Bayes rules and posterior risk.** Let the model be dominated, let the
  prior be a probability, and assume the marginal distribution of the
  observation is $\sigma$-finite. A rule minimizes the Bayes risk if and
  only if, for almost every observation under the marginal, its action
  minimizes the posterior expected loss. The minimal Bayes risk equals the
  marginal expectation of that minimal posterior expected loss.

* **34. Admissibility of Bayes rules.** A Bayes rule whose Bayes risk is
  finite, and which is unique up to almost-sure equality under every
  $P_\theta$, is admissible. If the prior charges every point of a finite
  parameter space, every Bayes rule of finite Bayes risk is admissible.

* **35. Constant risk and least favorable priors.** A Bayes rule whose risk
  is constant is minimax, and its prior is least favorable. Conversely, a
  least favorable prior and a corresponding Bayes rule of constant risk
  attain the minimax value.

* **36. Extended Bayes rules.** If a rule has constant risk $r$ and is
  extended Bayes, then it is minimax. In particular, a limit of Bayes risks
  equal to $r$ along priors that escape every compact set yields minimaxity
  of a constant-risk procedure.

* **37. Complete classes.** If $\Theta$ is finite and the action space is
  finite, or compact with continuous loss, then every admissible rule is
  Bayes for some prior, and the Bayes rules form a complete class. If
  $\Theta$ is a compact metric space, the action space is finite, and
  $\theta\mapsto R(\theta,a)$ is continuous for each action, the Bayes rules
  again form a complete class.

### A constant-risk example

* **38. Minimax estimation of a binomial proportion.** Let
  $X\sim\mathop{\mathrm{Bin}}(n,p)$ with $p\in[0,1]$ and squared-error loss.
  The posterior mean under the $\mathop{\mathrm{Beta}}(\sqrt n/2,\sqrt n/2)$
  prior is
  $$\delta(X)=\frac{X+\sqrt n/2}{n+\sqrt n},$$
  and its risk is the constant $1/\bigl(4(1+\sqrt n)^2\bigr)$. By item 35,
  $\delta$ is minimax and the beta prior is least favorable. The unbiased
  estimator $X/n$ has maximal risk $1/(4n)$, larger than the minimax value,
  but smaller risk than $\delta$ outside an interval around $p=1/2$ that
  shrinks as $n$ grows.

### Equivariance

A group $G$ acts measurably on the sample space, on $\Theta$, and on
$\mathcal A$. The model and the loss are **invariant** when the action on
samples pushes $P_\theta$ to $P_{g\theta}$ and
$L(g\theta,ga)=L(\theta,a)$. A rule is **equivariant** when it intertwines
the actions on the sample and on the action space. For a location family
the translations act by $x\mapsto x+g$ and $\theta\mapsto\theta+g$.

* **39. Hunt–Stein theorem.** Let the loss be invariant and bounded below. If
  $G$ is compact, Haar averaging produces an equivariant randomized
  rule whose risk at $\theta$ is the group average of the original risks
  at points in the orbit of $\theta$. Its maximum risk is no larger than
  the original maximum risk. The minimax value therefore equals the
  infimum over equivariant rules, and an equivariant minimax rule exists
  whenever a minimax rule exists. Averaging need not improve risk at
  each parameter point. For Euclidean translations, the Hunt–Stein
  argument uses asymptotically invariant probabilities; the analogous
  reduction holds under the usual compactness and lower-semicontinuity
  hypotheses ensuring an equivariant limit rule.

* **40. Pitman estimator of location.** Let $X_1,\ldots,X_n$ be independent
  with common density $f(x-\theta)$ on $\mathbb R$, and let the loss be
  squared error. Assume the integrals below are finite. The minimum-risk
  equivariant estimator is the formal posterior mean under Lebesgue measure,
  $$\delta(X)
  =\frac{\int u\prod_{i=1}^n f(X_i-u)\,du}
  {\int\prod_{i=1}^n f(X_i-u)\,du}.$$
  Its risk is finite and constant. By the Hunt–Stein theorem for
  translations it is minimax among all estimators, equivariant or not.

### Scale parameters

* **41. Pitman estimator of scale.** Let $X_1,\ldots,X_n$ be independent
  with common density $\sigma^{-1}f(x/\sigma)$ on $(0,\infty)$ or on
  $\mathbb R$, with $\sigma>0$, and let the loss be
  $(a-\sigma)^2/\sigma^2$. An estimator is scale equivariant when
  $\delta(cx)=c\,\delta(x)$ for $c>0$; such estimators have constant risk.
  Assume the integrals below are finite and positive. The minimum-risk
  scale-equivariant estimator is
  $$\delta(X)=\frac{\int_0^\infty v^{n}\prod_{i=1}^nf(vX_i)\,dv}
  {\int_0^\infty v^{n+1}\prod_{i=1}^nf(vX_i)\,dv},$$
  the formal Bayes rule for the prior $d\sigma/\sigma$. For an exponential
  sample with mean $\sigma$ it is $\sum_iX_i/(n+1)$; for a sample from
  $N(0,\sigma^2)$, the analogous estimator of $\sigma^2$ under the loss
  $(a/\sigma^2-1)^2$ is $\sum_iX_i^2/(n+2)$. For positive observations, the
  logarithmic transformation reduces the scale problem to the location
  problem of item 40.

### Exponential families and discrimination information

The natural exponential family, its cumulant function, and completeness are
items 4 and 5. Write $\mathcal N$ for the natural parameter
space and $A$ for the cumulant function.

* **42. Mean parameterization.** For a minimal full-rank exponential family
  with open natural parameter space, $\nabla A$ is a real-analytic
  diffeomorphism onto its image, the mean domain. This image lies in the
  interior of the convex support of the natural statistic. For a full
  steep family the image is the entire interior. Here steepness requires
  the norm of $\nabla A$ to diverge when an interior natural parameter
  approaches a finite boundary point of the natural parameter space.
  Surjectivity onto the convex-support interior does not hold for every
  nonsteep family. The covariance matrix is the Hessian of $A$.

* **43. Conditional exponential families.** Let the natural statistic split
  as $(T,S)$, with natural parameter $(\eta,\zeta)$. The conditional
  distribution of $T$ given $S=s$ is an exponential family with natural
  parameter $\eta$ and with cumulant function depending on $s$. The
  conditional distribution is free of $\zeta$. Conditioning on $S$ is the
  operation that removes this nuisance parameter inside the exponential
  family.

The **Kullback–Leibler divergence** of probability measures $P$ and $Q$ is
$$D(P\|Q)=\int\log\frac{dP}{dQ}\,dP$$
when $P$ is absolutely continuous with respect to $Q$ and the integral
exists in $(-\infty,\infty]$, and $D(P\|Q)=\infty$ otherwise.

* **44. Kullback–Leibler divergence.** $D(P\|Q)\ge 0$, with equality if and
  only if $P=Q$. For product measures,
  $D(P_1\otimes P_2\|Q_1\otimes Q_2)=D(P_1\|Q_1)+D(P_2\|Q_2)$.
  The chain rule for a joint law is
  $$D(P_{X,Y}\|Q_{X,Y})
  =D(P_X\|Q_X)+\mathbb E_{P_X} D(P_{Y\mid X}\|Q_{Y\mid X}).$$
  Consequently a Markov kernel acting on both measures cannot increase the
  divergence. The quadratic expansion of $D(P_{\theta+h}\|P_\theta)$ is
  SYNOPSIS102, item 13.

### Unbiased tests in exponential families

A level-$\alpha$ test of $H:\theta\in\Theta_0$ is **unbiased** when its power
is at least $\alpha$ throughout the alternative. It is **uniformly most
powerful unbiased** when it maximizes the power at every alternative among
all unbiased level-$\alpha$ tests. One-sided uniformly most powerful tests
are item 15. The statements here are the two-sided and nuisance
forms.

* **45. Two-sided tests in a one-parameter exponential family.** Let the
  model be a minimal exponential family of order one, with natural statistic
  $T$ and natural parameter in an open interval, and test $H:\eta=\eta_0$
  against $\eta\neq\eta_0$. A test that rejects for extreme values of $T$,
  with randomization only at the two critical points, and that satisfies
  $\mathbb E_{\eta_0}\varphi(T)=\alpha$ and
  $\mathbb E_{\eta_0}[T\varphi(T)]=\alpha\,\mathbb E_{\eta_0} T$,
  is uniformly most powerful unbiased of level $\alpha$.

* **46. Conditional tests with a nuisance parameter.** Let the model be a
  minimal exponential family with natural statistic $(T,S)$ and natural
  parameter $(\eta,\zeta)$, and test $H:\eta=\eta_0$ against $\eta\neq\eta_0$,
  with $\zeta$ unknown. The conditional law of $T$ given $S$ is free of
  $\zeta$. The two-sided test of item 45, applied conditionally on $S$ and
  so of conditional size $\alpha$, is uniformly most powerful unbiased of
  level $\alpha$. The same conditional construction, with a one-sided
  conditional test, is uniformly most powerful unbiased for a one-sided
  hypothesis on $\eta$.

### The generalized Neyman–Pearson lemma and similar tests

For a parameter set $\Theta\subset\mathbb R^k$ and hypotheses
$\Theta_0,\Theta_1$, the **boundary** is
$\omega=\overline{\Theta_0}\cap\overline{\Theta_1}$. A test $\varphi$ is
**$\alpha$-similar** on $\omega$ when $\mathbb E_\theta\varphi=\alpha$ for
every $\theta\in\omega$. If $T$ is sufficient for $\{P_\theta:\theta\in\omega\}$,
a test has **Neyman structure** with respect to $T$ when
$\mathbb E_\theta[\varphi\mid T]=\alpha$ almost surely for every
$\theta\in\omega$. A test with Neyman structure is $\alpha$-similar.

* **47. Generalized Neyman–Pearson lemma.** Let $f_0,f_1,\ldots,f_m$ be
  $\mu$-integrable real functions and $k_1,\ldots,k_m$ real constants, and
  let $\varphi_0$ be a test with $\varphi_0=1$ where
  $f_0>\sum_ik_if_i$ and $\varphi_0=0$ where $f_0<\sum_ik_if_i$. Then
  $\varphi_0$ maximizes $\int\varphi f_0\,d\mu$ among all tests $\varphi$
  satisfying
  $\int\varphi f_i\,d\mu\le\int\varphi_0f_i\,d\mu$ for each $i$ with
  $k_i>0$ and $\int\varphi f_i\,d\mu\ge\int\varphi_0f_i\,d\mu$ for each $i$
  with $k_i<0$. In particular it maximizes $\int\varphi f_0\,d\mu$ among
  tests with $\int\varphi f_i\,d\mu=\int\varphi_0f_i\,d\mu$ for every $i$.
  The functions $f_i$ need not be densities; in item 45 one of them is
  $T f_{\eta_0}$, which expresses the condition on the derivative of the
  power at $\eta_0$.

* **48. Unbiasedness and similarity.** Suppose the power function
  $\theta\mapsto\mathbb E_\theta\varphi$ of every test is continuous, as in
  an exponential family on the interior of its natural parameter space.
  Then every unbiased level-$\alpha$ test is $\alpha$-similar on $\omega$.
  Consequently a level-$\alpha$ test that is uniformly most powerful among
  $\alpha$-similar tests on $\omega$ is uniformly most powerful unbiased.

* **49. Neyman structure.** If $T$ is a boundedly complete sufficient
  statistic for $\{P_\theta:\theta\in\omega\}$, then every $\alpha$-similar
  test on $\omega$ has Neyman structure with respect to $T$. Maximizing the
  power among similar tests therefore reduces to maximizing the conditional
  power given $T=t$ for each $t$, subject to conditional size $\alpha$. In
  the setting of item 46 the statistic $S$ is complete and sufficient on
  the boundary $\eta=\eta_0$ by item 5, and this reduction,
  together with items 45 and 48, gives item 46.

### Interval hypotheses in one-parameter exponential families

In items 50 and 51 the model is a minimal exponential family of order one
with natural statistic $T$ and natural parameter $\eta$ in an open interval,
$\eta_1<\eta_2$ are interior points, and $\alpha\in(0,1)$.

* **50. Uniformly most powerful tests of a two-sided hypothesis.** For
  $H:\eta\le\eta_1$ or $\eta\ge\eta_2$ against $K:\eta_1<\eta<\eta_2$,
  there is a test with $\varphi=1$ when $c_1<T<c_2$, $\varphi=\gamma_i$ when
  $T=c_i$, and $\varphi=0$ when $T<c_1$ or $T>c_2$, where $c_1\le c_2$, such
  that $\mathbb E_{\eta_1}\varphi=\mathbb E_{\eta_2}\varphi=\alpha$. It is
  uniformly most powerful of level $\alpha$. Among tests with the same power
  at $\eta_1$ and $\eta_2$ it also minimizes the power at every
  $\eta<\eta_1$ and every $\eta>\eta_2$.

* **51. Uniformly most powerful unbiased tests of an interval
  hypothesis.** For $H:\eta_1\le\eta\le\eta_2$ against $\eta<\eta_1$ or
  $\eta>\eta_2$, the test that rejects when $T<c_1$ or $T>c_2$, randomizes
  at $c_1$ and $c_2$, and has $\mathbb E_{\eta_1}\varphi=
  \mathbb E_{\eta_2}\varphi=\alpha$ is uniformly most powerful unbiased of
  level $\alpha$. No uniformly most powerful level-$\alpha$ test exists for
  this problem. The complementary test $1-\varphi$ is of the form of
  item 50 at level $1-\alpha$. Item 45 is the limiting case
  $\eta_1=\eta_2$, in which the second side condition becomes a condition
  on the derivative of the power.

### Unbiased confidence sets and complete classes of tests

A confidence set $C$ of level $1-\alpha$ for $\theta$ is **unbiased** when
$P_\theta(\theta'\in C(X))\le1-\alpha$ for all $\theta'\ne\theta$; with a
nuisance parameter the condition is imposed for all values of the nuisance
parameter. It is **uniformly most accurate unbiased** when it minimizes
every such false-coverage probability among unbiased level-$(1-\alpha)$
confidence sets.

* **52. Uniformly most accurate unbiased confidence sets.** For each
  $\theta_0$, let $A(\theta_0)$ be the acceptance region of a
  nonrandomized uniformly most powerful unbiased level-$\alpha$ test of
  $\theta=\theta_0$ against $\theta\ne\theta_0$. Then
  $C(x)=\{\theta_0:x\in A(\theta_0)\}$ is a uniformly most accurate unbiased
  confidence set of level $1-\alpha$. By Pratt's theorem, item 30, it minimizes the expected length among unbiased confidence sets
  of that level at every parameter value. By items 45 and 46, the
  Student $t$ interval for a normal mean with unknown variance, the
  two-sample $t$ interval of item 20, and the normal-variance
  interval with the unbiased choice of chi-squared endpoints are uniformly
  most accurate unbiased; the equal-tailed variance interval of
  item 26, is not unbiased.

* **53. Karlin–Rubin complete class theorem.** Let a real-parameter family
  have monotone likelihood ratio in $T$, let the action space be
  $\{0,1\}$ (accept, reject), and let $\theta_0$ be such that
  $L(\theta,1)-L(\theta,0)>0$ for $\theta<\theta_0$ and
  $L(\theta,1)-L(\theta,0)<0$ for $\theta>\theta_0$. Then the one-sided
  tests, with $\varphi=1$ when $T>c$, $\varphi=\gamma$ when $T=c$, and
  $\varphi=0$ when $T<c$, for $c\in[-\infty,\infty]$ and
  $\gamma\in[0,1]$, form an essentially complete class: every test has a
  one-sided test whose risk is no larger at every $\theta$. The one-sided
  test matching the power of a given test at $\theta_0$ has no larger power
  below $\theta_0$ and no smaller power above it.

### Least favorable distributions

Let the null family $\{P_\vartheta:\vartheta\in\Theta_0\}$ be indexed
measurably, so that for a probability $\Lambda$ on $\Theta_0$ the mixture
$P_\Lambda=\int P_\vartheta\,\Lambda(d\vartheta)$ is a probability. A
distribution $\Lambda_0$ is **least favorable** for testing the null family
against a simple alternative $Q$ at level $\alpha$ when the most powerful
level-$\alpha$ test of $P_{\Lambda_0}$ against $Q$ has power no larger than
that of the most powerful test of $P_\Lambda$ against $Q$, for every
$\Lambda$.

* **54. Least favorable distributions.** Let $\varphi_0$ be most powerful
  of level $\alpha$ for $P_{\Lambda_0}$ against $Q$, and suppose
  $\mathbb E_\vartheta\varphi_0\le\alpha$ for every $\vartheta\in\Theta_0$.
  Then $\varphi_0$ is most powerful of level $\alpha$ for the composite
  null against $Q$, and $\Lambda_0$ is least favorable. If the power of
  $\varphi_0$ is less than one, $\Lambda_0$ is concentrated on
  $\{\vartheta:\mathbb E_\vartheta\varphi_0=\alpha\}$. For example, for a
  sample from $N(\mu,\sigma^2)$, $n\ge2$, the null $\sigma\le\sigma_0$ with
  $\mu$ unrestricted, and the alternative $(\mu_1,\sigma_1)$ with
  $\sigma_1>\sigma_0$, the normal law of mean $\mu_1$ and variance
  $(\sigma_1^2-\sigma_0^2)/n$ for $\mu$ at $\sigma=\sigma_0$ is least
  favorable. The resulting test rejects when
  $\sum_i(X_i-\bar X)^2>\sigma_0^2\chi^2_{n-1,1-\alpha}$; it does not depend
  on the alternative and is therefore uniformly most powerful for
  $\sigma\le\sigma_0$ against $\sigma>\sigma_0$.

### Invariant tests

A group $G$ acting measurably on the sample space leaves a testing problem
**invariant** when each $g$ maps the law $P_\theta$ to a law
$P_{\bar g\theta}$ and the induced map $\bar g$ preserves $\Theta_0$ and
$\Theta_1$. A test is **invariant** when $\varphi(gx)=\varphi(x)$ for all
$g$ and $x$. A statistic $M$ is a **maximal invariant** when it is
invariant and $M(x)=M(x')$ implies $x'=gx$ for some $g\in G$; it labels the
orbits. A test is **uniformly most powerful invariant** of level $\alpha$
when it is uniformly most powerful among invariant level-$\alpha$ tests.

* **55. Reduction by a maximal invariant.** A test is invariant if and
  only if it is a function of a maximal invariant $M$. The distribution of
  an invariant statistic depends on $\theta$ only through a maximal
  invariant $v(\theta)$ of the induced group on the parameter space.
  Hence, if the hypotheses are expressed in terms of $v(\theta)$ and the
  family of laws of $M$ is simple against simple, or has monotone
  likelihood ratio for one-sided hypotheses in $v(\theta)$, the
  Neyman–Pearson lemma or the Karlin–Rubin theorem, items 14 and 15, applied to $M$ gives a uniformly most powerful invariant test.
  Standard maximal invariants: differences $(x_1-x_n,\ldots,x_{n-1}-x_n)$
  for translations; the order statistic for permutations; the ranks for
  continuous increasing transformations of the coordinates; and
  $\|x\|$ for orthogonal transformations. For two location families with
  densities $f_0$ and $f_1$ on $\mathbb R^n$ and unknown common shift, the
  most powerful invariant test rejects for large values of
  $$\frac{\int f_1(x_1-u,\ldots,x_n-u)\,du}
  {\int f_0(x_1-u,\ldots,x_n-u)\,du}.$$
  In the standard examples invariance is applied after reduction to a
  sufficient statistic.

* **56. Normal tests as uniformly most powerful invariant tests.** For a
  sample from $N(\mu,\sigma^2)$, $n\ge2$, reduce to $(\bar X,S^2)$. The
  problem of testing $\mu\le0$ against $\mu>0$ is invariant under
  $x\mapsto cx$, $c>0$, with maximal invariant $t=\sqrt n\bar X/S$. Its law
  is the noncentral $t$ law on $n-1$ degrees of freedom with noncentrality
  $\sqrt n\mu/\sigma$, which has monotone likelihood ratio in $t$; the
  one-sided $t$ test is uniformly most powerful invariant. For $\mu=0$
  against $\mu\ne0$, adjoining $x\mapsto-x$ gives the maximal invariant
  $|t|$, and the two-sided $t$ test is uniformly most powerful invariant.
  The same holds for the two-sample $t$ tests of item 20,
  under location and scale changes, the noncentrality depending only on
  $(\mu_X-\mu_Y)/\sigma$. For the variance, translations give the maximal
  invariant $S^2$, and the one-sided chi-squared tests are uniformly most
  powerful invariant.

### The normal mean and simultaneous coverage

* **57. Estimation of a normal mean.** Let $X$ be $N_p(\theta,I_p)$ and let
  the loss be squared Euclidean error. The estimator $\delta_0(X)=X$ has
  risk $p$ at every $\theta$, and $p$ is the minimax risk in every
  dimension. For $p=1$ and $p=2$, $\delta_0$ is admissible. For $p\ge 3$,
  $\delta_0$ is minimax and inadmissible. The James–Stein estimator
  $$\delta(X)=\Bigl(1-\frac{p-2}{\|X\|^2}\Bigr)X$$
  has risk
  $p-(p-2)^2\mathbb E_\theta\bigl(\|X\|^{-2}\bigr)$, which is strictly less
  than $p$ for every $\theta$ and tends to $p$ as $\|\theta\|\to\infty$.
  The positive-part estimator that replaces the scalar factor by its
  positive part has risk no larger than the risk of $\delta$ at every
  $\theta$.

### Admissibility by limits of Bayes rules

* **58. Blyth's method.** Let $\Theta$ be a convex subset of Euclidean
  space with nonempty interior, suppose the rules with continuous risk
  functions form a complete class, and let $\delta_0$ have continuous risk.
  Suppose there are finite, possibly unnormalized, prior measures $\pi_n$
  with Bayes rules $\delta_n$ such that the Bayes risks
  $r(\pi_n,\delta_0)$ and $r(\pi_n,\delta_n)$ are finite; for every convex
  $C\subset\Theta$ with nonempty interior there are $K>0$ and $N$ with
  $\pi_n(C)\ge K$ for $n\ge N$; and
  $r(\pi_n,\delta_0)-r(\pi_n,\delta_n)\to0$. Then $\delta_0$ is
  admissible. For $X\sim N(\theta,1)$ and squared error, the unnormalized
  priors $\pi_n(d\theta)=\exp(-\theta^2/(2n))\,d\theta$ give
  $r(\pi_n,\delta_0)-r(\pi_n,\delta_n)=\sqrt{2\pi n}/(n+1)\to0$, which
  proves the one-dimensional admissibility of $X$ in item 57. Normalized
  $N(0,n)$ priors fail the mass condition.

### Simultaneous coverage

For simultaneous statements, a family of confidence sets has **simultaneous
coverage** $1-\alpha$ when the probability that every member covers its
target is $1-\alpha$.

* **59. Bonferroni method.** If $m$ confidence sets have coverages at least
  $1-\alpha/m$, then the probability that all $m$ cover their targets is at
  least $1-\alpha$.

* **60. Scheffé's method.** In the normal linear model
  $Y=X\beta+\varepsilon$ with $\varepsilon\sim N_n(0,\sigma^2 I_n)$ and
  $X$ of rank $r<n$, let $\hat\beta$ be a least-squares estimator,
  $\hat\sigma^2=\|Y-X\hat\beta\|^2/(n-r)$, and let $C$ be the column space of
  $X^\top$. Then
  $$\sup_{c\in C\setminus\{0\}}
  \frac{\bigl(c\cdot(\hat\beta-\beta)\bigr)^2}
  {\hat\sigma^2\,c^\top(X^\top X)^- c}
  =\frac{(\hat\beta-\beta)^\top X^\top X(\hat\beta-\beta)}{\hat\sigma^2},$$
  and the right-hand side has the law of $r F_{r,n-r}$. The intervals
  $$c\cdot\hat\beta
  \pm\hat\sigma\sqrt{r F_{r,n-r,1-\alpha}\,
  c^\top(X^\top X)^- c},
  \qquad c\in C,$$
  therefore cover $c\cdot\beta$ simultaneously with probability exactly
  $1-\alpha$.

* **61. Tukey's method.** In a balanced one-way normal layout with $a$
  groups of size $n$, common variance $\sigma^2$, and group means
  $\mu_1,\ldots,\mu_a$, let $\bar Y_i$ be the group means and let
  $\hat\sigma^2$ be the usual residual mean square on $\nu=a(n-1)$ degrees
  of freedom. If $q_{a,\nu,1-\alpha}$ is the upper $\alpha$ point of the
  studentized range for $a$ normal variables and $\nu$ degrees of freedom,
  the intervals
  $$\bar Y_i-\bar Y_j
  \pm q_{a,\nu,1-\alpha}\,\hat\sigma/\sqrt n$$
  cover $\mu_i-\mu_j$ for all pairs $(i,j)$ simultaneously with probability
  exactly $1-\alpha$ when the errors are normal.

### Comparison of experiments

An **experiment** is a dominated statistical model. Experiment
$\mathcal E$ is **more informative** than experiment $\mathcal F$, in
Blackwell's order, when every decision problem and every procedure based
on $\mathcal F$ can be matched by a procedure based on $\mathcal E$ whose
risk is no larger at every parameter value.

* **62. Blackwell's theorem.** Let $\mathcal E=\{P_\theta\}$ and
  $\mathcal F=\{Q_\theta\}$ be dominated experiments with the same finite
  parameter space. The following are equivalent. The experiment
  $\mathcal E$ is more informative than $\mathcal F$. There is a Markov
  kernel $K$ from the sample space of $\mathcal E$ to the sample space of
  $\mathcal F$ such that $Q_\theta=\int K(x,\cdot)\,P_\theta(dx)$ for every
  $\theta$. For every finite action space and every bounded loss, every
  risk function available from $\mathcal F$ is available from $\mathcal E$.
  A sufficient statistic realizes the equivalence case: the experiment that
  reports only the sufficient statistic is equivalent to the original
  experiment. Le Cam's deficiency extends the comparison to a quantitative
  distance between experiments with general parameter spaces; the finite
  Blackwell order is the case of deficiency zero.

### Further bounds, shrinkage, and simultaneous testing

* **63. Chapman–Robbins inequality.** Let $T$ be an unbiased estimator of
  $g(\theta)$ with finite variance. For every $\theta'$ with
  $P_{\theta'}\ll P_\theta$ and finite positive denominator,
  $$\mathop{\mathrm{Var}}_\theta T\ge
  \frac{(g(\theta')-g(\theta))^2}
  {\mathbb E_\theta[(dP_{\theta'}/dP_\theta-1)^2]}.$$
  Taking the supremum gives a bound without differentiation or a common
  support assumption. Under regularity, letting $\theta'\to\theta$
  recovers the scalar information inequality of item 10.

* **64. Stein's identity and unbiased risk estimation.** Let
  $X\sim N_p(\theta,\sigma^2I)$, with known $\sigma^2>0$. For weakly
  differentiable $g:\mathbb R^p\to\mathbb R^p$ satisfying
  $\mathbb E\|g(X)\|^2<\infty$ and
  $\mathbb E|\partial_i g_i(X)|<\infty$,
  $$\mathbb E[(X_i-\theta_i)g_i(X)]
  =\sigma^2\mathbb E\partial_i g_i(X).$$
  Consequently the squared-error risk of $X+g(X)$ is the expectation of
  $$p\sigma^2+\|g(X)\|^2+2\sigma^2\sum_i\partial_i g_i(X).$$
  This is Stein's unbiased risk estimate. With $g(x)=-(p-2)x/\|x\|^2$
  and $\sigma=1$ it yields the risk formula in item 57.

* **65. Information with a nuisance parameter.** In a regular model with
  parameter $(\psi,\lambda)$, partition the information as
  $$I=\begin{pmatrix}I_{\psi\psi}&I_{\psi\lambda}\\
  I_{\lambda\psi}&I_{\lambda\lambda}\end{pmatrix}.$$
  If $I$ is positive definite, the information for $\psi$ when $\lambda$
  is unknown is
  $$I_{\psi\cdot\lambda}
  =I_{\psi\psi}-I_{\psi\lambda}I_{\lambda\lambda}^{-1}I_{\lambda\psi}.$$
  An unbiased estimator of $\psi$ has covariance at least
  $I_{\psi\cdot\lambda}^{-1}$. The efficient score is
  $\ell_\psi-I_{\psi\lambda}I_{\lambda\lambda}^{-1}\ell_\lambda$.
  Orthogonal nuisance scores cause no information loss. Projection onto
  an infinite-dimensional nuisance space is SYNOPSIS102, item 34.

* **66. Testing and total variation.** For two probability laws $P,Q$,
  define $\|P-Q\|_{\mathrm{TV}}=\sup_A|P(A)-Q(A)|$. Then
  $$\inf_{0\le\varphi\le1}\{P\varphi+Q(1-\varphi)\}
  =1-\|P-Q\|_{\mathrm{TV}}.$$
  A likelihood-ratio test with threshold one attains the infimum.
  Furthermore $\|P-Q\|_{\mathrm{TV}}\le\sqrt{D(P\|Q)/2}$.
  These comparisons turn indistinguishability into estimation lower bounds;
  see SYNOPSIS103, item 39.

A procedure **strongly controls family-wise error** at level $\alpha$ when
the probability of even one false rejection is at most $\alpha$ under
every configuration of true and false null hypotheses. Each individual
null $p$-value below is valid in the sense of item 25.

* **67. Holm's step-down procedure.** Order $m$ $p$-values as
  $p_{(1)}\le\cdots\le p_{(m)}$. Starting at $j=1$, reject the $j$th
  hypothesis if $p_{(j)}\le\alpha/(m-j+1)$, stopping at the first failure.
  This procedure strongly controls family-wise error under arbitrary
  dependence and contains every rejection of the Bonferroni procedure.

* **68. Closed testing principle.** For every nonempty subset $J$ of the
  hypotheses, choose a level-$\alpha$ test of their intersection $H_J$.
  Reject an elementary $H_i$ only if every $H_J$ containing it is rejected.
  The resulting procedure strongly controls family-wise error at level
  $\alpha$, regardless of dependence. Bonferroni local tests yield Holm's
  procedure as a computational shortcut.

### Likelihood and convex geometry

* **69. Existence of an exponential-family maximum.** In a minimal regular
  natural exponential family with cumulant $A$, an independent sample has
  log-likelihood $n(\eta\cdot\bar T-A(\eta))$ up to an additive constant.
  A finite maximum in the open natural parameter space exists if and only
  if $\bar T$ lies in $\nabla A(\mathcal N)$. It is unique and solves
  $\nabla A(\hat\eta)=\bar T$. In a steep full family this mean domain is
  the interior of the convex support. Boundary empirical means may yield
  only a supremum, as in a Bernoulli sample containing only successes.

* **70. Divergence in an exponential family.** For two interior natural
  parameters,
  $$D(P_\eta\|P_\zeta)
  =A(\zeta)-A(\eta)-\nabla A(\eta)\cdot(\zeta-\eta).$$
  Thus relative entropy is the Bregman divergence of the cumulant function
  with this order of arguments. Its local quadratic term is
  $\tfrac12(\zeta-\eta)^\top\nabla^2A(\eta)(\zeta-\eta)$.

### Distribution handbooks and history

Johnson, Kotz, and Balakrishnan, and Kendall's *Advanced Theory*, record
densities, moments, and relations among the classical families used in the
statements above. Stigler, Hald, and Lehmann's historical essay record the
provenance of sufficiency, likelihood, least squares, and the Neyman–Pearson
theory. Those sources do not add a further numbered list in this selection.

## Reference guide

### Correspondence with the subdivisions

- **[101A](CKSD-bib.md#cks-101a)**: Casella–Berger, Schervish, Cox–Hinkley,
  Bickel–Doksum, Borovkov, Cramér, and Pfanzagl develop the factorization
  theorem, exponential families, completeness, the information inequality, the
  Neyman–Pearson and Karlin–Rubin theorems, and the normal sampling laws.
- **[101B](CKSD-bib.md#cks-101b)**: The distribution catalogues and the
  histories support formulae and attribution. They are not given numbered
  entries in this pass.

### Source comparisons and local copies

#### General graduate texts

The expanded sampling and exact-inference group uses Casella–Berger,
Section 5.4 (Theorems 5.4.4 and 5.4.6 and the uniform-order-statistic
example), Section 8.3.4 (validity of tail and conditional $p$-values and
Example 8.3.30), and Section 9.2 with Exercise 9.21 (exact binomial
intervals). These passages were read in the local copy. The quantile
confidence formula follows by counting observations below the quantile;
the variance interval uses the pivot in item 17. Item 27 records the
squared-error consequences of conditional projection, rather than
introducing a separate probability theorem.

The third expansion (items 12, 13, 19, 20, and 28–31) uses Casella–Berger, Theorems 7.3.19
and 7.3.20 and Example 7.3.21 (unbiased estimators of zero), Definition
8.2.1, Theorem 8.2.4, and Examples 8.2.2, 8.2.6 and Exercise 8.41 (likelihood
ratio tests and the two-sample $t$ test), Definition 9.2.6 and Examples
9.2.7 and 9.2.8 (location–scale and gamma pivots), and Theorems 9.3.2 and
9.3.9 (shortest unimodal intervals and Pratt's theorem). Pratt's theorem is
stated in the Fubini form of Young–Smith, Section 7.3, rather than with the
monotone endpoints of Casella–Berger. Shao's exercise volume records the
UMVU criterion and the Watson–Royall completeness of order statistics as
Theorems 3.2 and 3.13 of his main text. Item 13 follows Pfanzagl,
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
this material. They are not in the local reference
directory. Shao's *Mathematical Statistics* and Keener's *Theoretical
Statistics* are likewise absent locally; Shao's companion exercise volume is
present and cites the theorem numbers of the main text. The numbered statements were
matched to the local texts listed below.

#### Decision theory, estimation, and testing

For the expansion, Schervish's Theorem 5.18 was read for item 63.
Ferguson's Section 4.2 gives the averaging argument: its inequality is for
maximum risk, as now stated in item 39. Berger's normal-mean discussion
supplies the risk-estimation framework of item 64. Item 65 is the block
information inequality, and items 69 and 70 specialize the exponential-family
geometry of Brown and Barndorff-Nielsen. The qualification by steepness
in item 42 distinguishes the mean domain from the entire convex-support
interior. Holm and closed testing extend the simultaneous-inference
material; their error control uses valid marginal and intersection tests,
without independence assumptions.

The third expansion (items 38, 41, 47–56, and 58) was checked against the following
passages. Item 38 is Schervish, Section 3.2.4 (the binomial example with
a beta prior). Item 41 follows Berger, Section 6.4 (reduction of scale to
location by logarithms), with the formula checked on the exponential case
and on the scale exercises of Shao's exercise volume. Items 47–49
are Schervish, Lemma 4.78, Proposition 4.92 with Lemma 4.96, and
Lemma 4.122 with Definition 4.120; Cox–Hinkley, Section 5.2, gives the same
Neyman-structure argument. Items 50 and 51 are Schervish, Theorem 4.82 and
Theorem 4.100, Section 4.4.2; the limiting point-hypothesis case is his
Theorem 4.104. Item 52 is Schervish, Definition 5.60 and Proposition 5.61,
Ferguson, Section 5.8, and Young–Smith, Section 7.3, which also gives the
expected-length interpretation. Item 53 is Schervish, Theorem 4.68.
Item 54 is Pfanzagl, Proposition 4.4.2 and Example 4.4.5, after Lehmann
and Stein. Items 55 and 56 are Ferguson, Section 5.6 (Theorems 1 and 2, the
listed maximal invariants, and the $t$-test examples with Exercises 5.6.4–
5.6.6), Berger, Section 6.5, and Cox–Hinkley, Section 5.3. Item 58 is
Berger, Section 8.9.2, Theorem 13 and Example 10 (Blyth, 1951).

Ferguson, Chapters 1, 2, 4, and 5, is the course-length source for the
minimax theorem, complete classes, invariance, and testing. Schervish,
Chapters 3–6, develops Bayes rules, admissibility, equivariance, and the
normal-mean problem with the measure theory in place. Cox–Hinkley,
Chapters 4, 5, and 11, treats Neyman structure, unbiased tests, and the
decision-theoretic formulation, including the inadmissibility phenomenon of
item 57. Pfanzagl, Chapters 4 and 5, gives the uniformly most powerful
unbiased tests for exponential families and the passage from those tests to
confidence bounds. Berger is the graduate reference that carries Bayes
rules, minimaxity, invariance, and the James–Stein estimator in one
development. Blackwell and Girshick, and Wald's monograph, are the classical
sources for the game-theoretic theorems and for comparison of experiments.
Brown and Barndorff-Nielsen supply the convex geometry of exponential
families used in items 42 and 43. Kullback is the source for the divergence
in item 44. Miller is the monograph for items 59–61; Scheffé's *Analysis of
Variance* is the source for the simultaneous $F$ bounds.

Lehmann and Casella, *Theory of Point Estimation*, and Lehmann and Romano,
*Testing Statistical Hypotheses*, are not in the local reference directory.
Torgersen's comparison monograph is present as a DjVu file and was not
text-extracted for this pass; item 62 is the finite-parameter theorem shared
by Ferguson and by Blackwell and Girshick. The local Blackwell–Girshick and
Wald scans have no extractable outline; the numbered statements were checked
against Ferguson, Schervish, Cox–Hinkley, and Pfanzagl.

Local texts directly consulted or identified for this selection:

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
- [Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*](../lean-CKMA/References/Ferguson1967MathematicalStatisticsDecisionTheoreticApproach-AcademicPress.ProbMathStat.pdf).
- [Barndorff-Nielsen, *Information and Exponential Families*](../lean-CKMA/References/BarndorffNielsen1978rep2014InformationExponentialFamiliesStatisticalTheory-WileySerProbStat.pdf).
- [Kullback, *Information Theory and Statistics*](../lean-CKMA/References/Kullback1978InformationTheoryStatistics-PeterSmith.pdf).
- [Miller, *Simultaneous Statistical Inference*](../lean-CKMA/References/Miller1981SimultaneousStatisticalInference2ndEd-Springer.SSS.pdf).
- [Scheffé, *The Analysis of Variance*](../lean-CKMA/References/Scheffé1959AnalysisVariance-Wiley.pdf).
- [Blackwell and Girshick, *Theory of Games and Statistical Decisions*](../lean-CKMA/References/BlackwellGirshick1979TheoryGamesStatisticalDecisions-Dover.pdf).
- [Wald, *Statistical Decision Functions*](../lean-CKMA/References/Wald1950StatisticalDecisionFunctions-Wiley.pdf).
