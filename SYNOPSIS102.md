# Synopsis: Classical inference: decision theory, estimation, and testing

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-102).

This synopsis is the finite-sample decision theory of Section 102. The
first-course forms of sufficiency, the information inequality, and
uniformly most powerful one-sided tests are
[SYNOPSIS101](SYNOPSIS101.md), items 1–13. Asymptotic optimality is
[SYNOPSIS103](SYNOPSIS103.md). Bayesian foundations beyond the Bayes rule
used here, and Monte Carlo methods, are in Section 105. Large-scale multiple
testing is in Section 107. The normal linear model is developed in
Section 106; the simultaneous procedures below use only as much of that
model as their statements need.

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

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

## Finite decision problems

* **1. Value of a finite statistical game.** If $\Theta$ and $\mathcal A$
  are finite, the statistical game has a value: the minimax risk equals
  the supremum over priors of the minimal Bayes risk. A minimax rule exists,
  and a least favorable prior exists. Priors are mixed strategies for
  nature, and randomized rules are mixed strategies for the statistician.

* **2. Bayes rules and posterior risk.** Let the model be dominated, let the
  prior be a probability, and assume the marginal distribution of the
  observation is $\sigma$-finite. A rule minimizes the Bayes risk if and
  only if, for almost every observation under the marginal, its action
  minimizes the posterior expected loss. The minimal Bayes risk equals the
  marginal expectation of that minimal posterior expected loss.

* **3. Admissibility of Bayes rules.** A Bayes rule whose Bayes risk is
  finite, and which is unique up to almost-sure equality under every
  $P_\theta$, is admissible. If the prior charges every point of a finite
  parameter space, every Bayes rule of finite Bayes risk is admissible.

* **4. Constant risk and least favorable priors.** A Bayes rule whose risk
  is constant is minimax, and its prior is least favorable. Conversely, a
  least favorable prior and a corresponding Bayes rule of constant risk
  attain the minimax value.

* **5. Extended Bayes rules.** If a rule has constant risk $r$ and is
  extended Bayes, then it is minimax. In particular, a limit of Bayes risks
  equal to $r$ along priors that escape every compact set yields minimaxity
  of a constant-risk procedure.

* **6. Complete classes.** If $\Theta$ is finite and the action space is
  finite, or compact with continuous loss, then every admissible rule is
  Bayes for some prior, and the Bayes rules form a complete class. If
  $\Theta$ is a compact metric space, the action space is finite, and
  $\theta\mapsto R(\theta,a)$ is continuous for each action, the Bayes rules
  again form a complete class.

### A constant-risk example

* **27. Minimax estimation of a binomial proportion.** Let
  $X\sim\mathop{\mathrm{Bin}}(n,p)$ with $p\in[0,1]$ and squared-error loss.
  The posterior mean under the $\mathop{\mathrm{Beta}}(\sqrt n/2,\sqrt n/2)$
  prior is
  $$\delta(X)=\frac{X+\sqrt n/2}{n+\sqrt n},$$
  and its risk is the constant $1/\bigl(4(1+\sqrt n)^2\bigr)$. By item 4,
  $\delta$ is minimax and the beta prior is least favorable. The unbiased
  estimator $X/n$ has maximal risk $1/(4n)$, larger than the minimax value,
  but smaller risk than $\delta$ outside an interval around $p=1/2$ that
  shrinks as $n$ grows.

## Equivariance

A group $G$ acts measurably on the sample space, on $\Theta$, and on
$\mathcal A$. The model and the loss are **invariant** when the action on
samples pushes $P_\theta$ to $P_{g\theta}$ and
$L(g\theta,ga)=L(\theta,a)$. A rule is **equivariant** when it intertwines
the actions on the sample and on the action space. For a location family
the translations act by $x\mapsto x+g$ and $\theta\mapsto\theta+g$.

* **7. Hunt–Stein theorem.** Let the loss be invariant and bounded below. If
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

* **8. Pitman estimator of location.** Let $X_1,\ldots,X_n$ be independent
  with common density $f(x-\theta)$ on $\mathbb R$, and let the loss be
  squared error. Assume the integrals below are finite. The minimum-risk
  equivariant estimator is the formal posterior mean under Lebesgue measure,
  $$\delta(X)
  =\frac{\int u\prod_{i=1}^n f(X_i-u)\,du}
  {\int\prod_{i=1}^n f(X_i-u)\,du}.$$
  Its risk is finite and constant. By the Hunt–Stein theorem for
  translations it is minimax among all estimators, equivariant or not.

### Scale parameters

* **28. Pitman estimator of scale.** Let $X_1,\ldots,X_n$ be independent
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
  problem of item 8.

## Exponential families and discrimination information

The natural exponential family, its cumulant function, and completeness are
SYNOPSIS101, items 4 and 5. Write $\mathcal N$ for the natural parameter
space and $A$ for the cumulant function.

* **9. Mean parameterization.** For a minimal full-rank exponential family
  with open natural parameter space, $\nabla A$ is a real-analytic
  diffeomorphism onto its image, the mean domain. This image lies in the
  interior of the convex support of the natural statistic. For a full
  steep family the image is the entire interior. Here steepness requires
  the norm of $\nabla A$ to diverge when an interior natural parameter
  approaches a finite boundary point of the natural parameter space.
  Surjectivity onto the convex-support interior does not hold for every
  nonsteep family. The covariance matrix is the Hessian of $A$.

* **10. Conditional exponential families.** Let the natural statistic split
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

* **11. Kullback–Leibler divergence.** $D(P\|Q)\ge 0$, with equality if and
  only if $P=Q$. For product measures,
  $D(P_1\otimes P_2\|Q_1\otimes Q_2)=D(P_1\|Q_1)+D(P_2\|Q_2)$.
  The chain rule for a joint law is
  $$D(P_{X,Y}\|Q_{X,Y})
  =D(P_X\|Q_X)+\mathbb E_{P_X} D(P_{Y\mid X}\|Q_{Y\mid X}).$$
  Consequently a Markov kernel acting on both measures cannot increase the
  divergence. The quadratic expansion of $D(P_{\theta+h}\|P_\theta)$ is
  SYNOPSIS103, item 9.

## Unbiased tests in exponential families

A level-$\alpha$ test of $H:\theta\in\Theta_0$ is **unbiased** when its power
is at least $\alpha$ throughout the alternative. It is **uniformly most
powerful unbiased** when it maximizes the power at every alternative among
all unbiased level-$\alpha$ tests. One-sided uniformly most powerful tests
are SYNOPSIS101, item 13. The statements here are the two-sided and nuisance
forms.

* **12. Two-sided tests in a one-parameter exponential family.** Let the
  model be a minimal exponential family of order one, with natural statistic
  $T$ and natural parameter in an open interval, and test $H:\eta=\eta_0$
  against $\eta\neq\eta_0$. A test that rejects for extreme values of $T$,
  with randomization only at the two critical points, and that satisfies
  $\mathbb E_{\eta_0}\varphi(T)=\alpha$ and
  $\mathbb E_{\eta_0}[T\varphi(T)]=\alpha\,\mathbb E_{\eta_0} T$,
  is uniformly most powerful unbiased of level $\alpha$.

* **13. Conditional tests with a nuisance parameter.** Let the model be a
  minimal exponential family with natural statistic $(T,S)$ and natural
  parameter $(\eta,\zeta)$, and test $H:\eta=\eta_0$ against $\eta\neq\eta_0$,
  with $\zeta$ unknown. The conditional law of $T$ given $S$ is free of
  $\zeta$. The two-sided test of item 12, applied conditionally on $S$ and
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

* **29. Generalized Neyman–Pearson lemma.** Let $f_0,f_1,\ldots,f_m$ be
  $\mu$-integrable real functions and $k_1,\ldots,k_m$ real constants, and
  let $\varphi_0$ be a test with $\varphi_0=1$ where
  $f_0>\sum_ik_if_i$ and $\varphi_0=0$ where $f_0<\sum_ik_if_i$. Then
  $\varphi_0$ maximizes $\int\varphi f_0\,d\mu$ among all tests $\varphi$
  satisfying
  $\int\varphi f_i\,d\mu\le\int\varphi_0f_i\,d\mu$ for each $i$ with
  $k_i>0$ and $\int\varphi f_i\,d\mu\ge\int\varphi_0f_i\,d\mu$ for each $i$
  with $k_i<0$. In particular it maximizes $\int\varphi f_0\,d\mu$ among
  tests with $\int\varphi f_i\,d\mu=\int\varphi_0f_i\,d\mu$ for every $i$.
  The functions $f_i$ need not be densities; in item 12 one of them is
  $T f_{\eta_0}$, which expresses the condition on the derivative of the
  power at $\eta_0$.

* **30. Unbiasedness and similarity.** Suppose the power function
  $\theta\mapsto\mathbb E_\theta\varphi$ of every test is continuous, as in
  an exponential family on the interior of its natural parameter space.
  Then every unbiased level-$\alpha$ test is $\alpha$-similar on $\omega$.
  Consequently a level-$\alpha$ test that is uniformly most powerful among
  $\alpha$-similar tests on $\omega$ is uniformly most powerful unbiased.

* **31. Neyman structure.** If $T$ is a boundedly complete sufficient
  statistic for $\{P_\theta:\theta\in\omega\}$, then every $\alpha$-similar
  test on $\omega$ has Neyman structure with respect to $T$. Maximizing the
  power among similar tests therefore reduces to maximizing the conditional
  power given $T=t$ for each $t$, subject to conditional size $\alpha$. In
  the setting of item 13 the statistic $S$ is complete and sufficient on
  the boundary $\eta=\eta_0$ by SYNOPSIS101, item 5, and this reduction,
  together with items 12 and 30, gives item 13.

### Interval hypotheses in one-parameter exponential families

In items 32 and 33 the model is a minimal exponential family of order one
with natural statistic $T$ and natural parameter $\eta$ in an open interval,
$\eta_1<\eta_2$ are interior points, and $\alpha\in(0,1)$.

* **32. Uniformly most powerful tests of a two-sided hypothesis.** For
  $H:\eta\le\eta_1$ or $\eta\ge\eta_2$ against $K:\eta_1<\eta<\eta_2$,
  there is a test with $\varphi=1$ when $c_1<T<c_2$, $\varphi=\gamma_i$ when
  $T=c_i$, and $\varphi=0$ when $T<c_1$ or $T>c_2$, where $c_1\le c_2$, such
  that $\mathbb E_{\eta_1}\varphi=\mathbb E_{\eta_2}\varphi=\alpha$. It is
  uniformly most powerful of level $\alpha$. Among tests with the same power
  at $\eta_1$ and $\eta_2$ it also minimizes the power at every
  $\eta<\eta_1$ and every $\eta>\eta_2$.

* **33. Uniformly most powerful unbiased tests of an interval
  hypothesis.** For $H:\eta_1\le\eta\le\eta_2$ against $\eta<\eta_1$ or
  $\eta>\eta_2$, the test that rejects when $T<c_1$ or $T>c_2$, randomizes
  at $c_1$ and $c_2$, and has $\mathbb E_{\eta_1}\varphi=
  \mathbb E_{\eta_2}\varphi=\alpha$ is uniformly most powerful unbiased of
  level $\alpha$. No uniformly most powerful level-$\alpha$ test exists for
  this problem. The complementary test $1-\varphi$ is of the form of
  item 32 at level $1-\alpha$. Item 12 is the limiting case
  $\eta_1=\eta_2$, in which the second side condition becomes a condition
  on the derivative of the power.

### Unbiased confidence sets and complete classes of tests

A confidence set $C$ of level $1-\alpha$ for $\theta$ is **unbiased** when
$P_\theta(\theta'\in C(X))\le1-\alpha$ for all $\theta'\ne\theta$; with a
nuisance parameter the condition is imposed for all values of the nuisance
parameter. It is **uniformly most accurate unbiased** when it minimizes
every such false-coverage probability among unbiased level-$(1-\alpha)$
confidence sets.

* **34. Uniformly most accurate unbiased confidence sets.** For each
  $\theta_0$, let $A(\theta_0)$ be the acceptance region of a
  nonrandomized uniformly most powerful unbiased level-$\alpha$ test of
  $\theta=\theta_0$ against $\theta\ne\theta_0$. Then
  $C(x)=\{\theta_0:x\in A(\theta_0)\}$ is a uniformly most accurate unbiased
  confidence set of level $1-\alpha$. By Pratt's theorem, SYNOPSIS101,
  item 30, it minimizes the expected length among unbiased confidence sets
  of that level at every parameter value. By items 12 and 13, the
  Student $t$ interval for a normal mean with unknown variance, the
  two-sample $t$ interval of SYNOPSIS101, item 27, and the normal-variance
  interval with the unbiased choice of chi-squared endpoints are uniformly
  most accurate unbiased; the equal-tailed variance interval of
  SYNOPSIS101, item 22, is not unbiased.

* **35. Karlin–Rubin complete class theorem.** Let a real-parameter family
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

## Composite hypotheses: least favorable distributions and invariance

### Least favorable distributions

Let the null family $\{P_\vartheta:\vartheta\in\Theta_0\}$ be indexed
measurably, so that for a probability $\Lambda$ on $\Theta_0$ the mixture
$P_\Lambda=\int P_\vartheta\,\Lambda(d\vartheta)$ is a probability. A
distribution $\Lambda_0$ is **least favorable** for testing the null family
against a simple alternative $Q$ at level $\alpha$ when the most powerful
level-$\alpha$ test of $P_{\Lambda_0}$ against $Q$ has power no larger than
that of the most powerful test of $P_\Lambda$ against $Q$, for every
$\Lambda$.

* **36. Least favorable distributions.** Let $\varphi_0$ be most powerful
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

* **37. Reduction by a maximal invariant.** A test is invariant if and
  only if it is a function of a maximal invariant $M$. The distribution of
  an invariant statistic depends on $\theta$ only through a maximal
  invariant $v(\theta)$ of the induced group on the parameter space.
  Hence, if the hypotheses are expressed in terms of $v(\theta)$ and the
  family of laws of $M$ is simple against simple, or has monotone
  likelihood ratio for one-sided hypotheses in $v(\theta)$, the
  Neyman–Pearson lemma or the Karlin–Rubin theorem, SYNOPSIS101, items 12
  and 13, applied to $M$ gives a uniformly most powerful invariant test.
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

* **38. Normal tests as uniformly most powerful invariant tests.** For a
  sample from $N(\mu,\sigma^2)$, $n\ge2$, reduce to $(\bar X,S^2)$. The
  problem of testing $\mu\le0$ against $\mu>0$ is invariant under
  $x\mapsto cx$, $c>0$, with maximal invariant $t=\sqrt n\bar X/S$. Its law
  is the noncentral $t$ law on $n-1$ degrees of freedom with noncentrality
  $\sqrt n\mu/\sigma$, which has monotone likelihood ratio in $t$; the
  one-sided $t$ test is uniformly most powerful invariant. For $\mu=0$
  against $\mu\ne0$, adjoining $x\mapsto-x$ gives the maximal invariant
  $|t|$, and the two-sided $t$ test is uniformly most powerful invariant.
  The same holds for the two-sample $t$ tests of SYNOPSIS101, item 27,
  under location and scale changes, the noncentrality depending only on
  $(\mu_X-\mu_Y)/\sigma$. For the variance, translations give the maximal
  invariant $S^2$, and the one-sided chi-squared tests are uniformly most
  powerful invariant.

## The normal mean and simultaneous coverage

* **14. Estimation of a normal mean.** Let $X$ be $N_p(\theta,I_p)$ and let
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

* **39. Blyth's method.** Let $\Theta$ be a convex subset of Euclidean
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
  proves the one-dimensional admissibility of $X$ in item 14. Normalized
  $N(0,n)$ priors fail the mass condition.

### Simultaneous coverage

For simultaneous statements, a family of confidence sets has **simultaneous
coverage** $1-\alpha$ when the probability that every member covers its
target is $1-\alpha$.

* **15. Bonferroni method.** If $m$ confidence sets have coverages at least
  $1-\alpha/m$, then the probability that all $m$ cover their targets is at
  least $1-\alpha$.

* **16. Scheffé's method.** In the normal linear model
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

* **17. Tukey's method.** In a balanced one-way normal layout with $a$
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

## Comparison of experiments

An **experiment** is a dominated statistical model. Experiment
$\mathcal E$ is **more informative** than experiment $\mathcal F$, in
Blackwell's order, when every decision problem and every procedure based
on $\mathcal F$ can be matched by a procedure based on $\mathcal E$ whose
risk is no larger at every parameter value.

* **18. Blackwell's theorem.** Let $\mathcal E=\{P_\theta\}$ and
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

## Further bounds, shrinkage, and simultaneous testing

* **19. Chapman–Robbins inequality.** Let $T$ be an unbiased estimator of
  $g(\theta)$ with finite variance. For every $\theta'$ with
  $P_{\theta'}\ll P_\theta$ and finite positive denominator,
  $$\mathop{\mathrm{Var}}_\theta T\ge
  \frac{(g(\theta')-g(\theta))^2}
  {\mathbb E_\theta[(dP_{\theta'}/dP_\theta-1)^2]}.$$
  Taking the supremum gives a bound without differentiation or a common
  support assumption. Under regularity, letting $\theta'\to\theta$
  recovers the scalar information inequality of SYNOPSIS101, item 10.

* **20. Stein's identity and unbiased risk estimation.** Let
  $X\sim N_p(\theta,\sigma^2I)$, with known $\sigma^2>0$. For weakly
  differentiable $g:\mathbb R^p\to\mathbb R^p$ satisfying
  $\mathbb E\|g(X)\|^2<\infty$ and
  $\mathbb E|\partial_i g_i(X)|<\infty$,
  $$\mathbb E[(X_i-\theta_i)g_i(X)]
  =\sigma^2\mathbb E\partial_i g_i(X).$$
  Consequently the squared-error risk of $X+g(X)$ is the expectation of
  $$p\sigma^2+\|g(X)\|^2+2\sigma^2\sum_i\partial_i g_i(X).$$
  This is Stein's unbiased risk estimate. With $g(x)=-(p-2)x/\|x\|^2$
  and $\sigma=1$ it yields the risk formula in item 14.

* **21. Information with a nuisance parameter.** In a regular model with
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
  an infinite-dimensional nuisance space is SYNOPSIS104, item 14.

* **22. Testing and total variation.** For two probability laws $P,Q$,
  define $\|P-Q\|_{\mathrm{TV}}=\sup_A|P(A)-Q(A)|$. Then
  $$\inf_{0\le\varphi\le1}\{P\varphi+Q(1-\varphi)\}
  =1-\|P-Q\|_{\mathrm{TV}}.$$
  A likelihood-ratio test with threshold one attains the infimum.
  Furthermore $\|P-Q\|_{\mathrm{TV}}\le\sqrt{D(P\|Q)/2}$.
  These comparisons turn indistinguishability into estimation lower bounds;
  see SYNOPSIS107, item 14.

A procedure **strongly controls family-wise error** at level $\alpha$ when
the probability of even one false rejection is at most $\alpha$ under
every configuration of true and false null hypotheses. Each individual
null $p$-value below is valid in the sense of SYNOPSIS101, item 21.

* **23. Holm's step-down procedure.** Order $m$ $p$-values as
  $p_{(1)}\le\cdots\le p_{(m)}$. Starting at $j=1$, reject the $j$th
  hypothesis if $p_{(j)}\le\alpha/(m-j+1)$, stopping at the first failure.
  This procedure strongly controls family-wise error under arbitrary
  dependence and contains every rejection of the Bonferroni procedure.

* **24. Closed testing principle.** For every nonempty subset $J$ of the
  hypotheses, choose a level-$\alpha$ test of their intersection $H_J$.
  Reject an elementary $H_i$ only if every $H_J$ containing it is rejected.
  The resulting procedure strongly controls family-wise error at level
  $\alpha$, regardless of dependence. Bonferroni local tests yield Holm's
  procedure as a computational shortcut.

## Likelihood and convex geometry

* **25. Existence of an exponential-family maximum.** In a minimal regular
  natural exponential family with cumulant $A$, an independent sample has
  log-likelihood $n(\eta\cdot\bar T-A(\eta))$ up to an additive constant.
  A finite maximum in the open natural parameter space exists if and only
  if $\bar T$ lies in $\nabla A(\mathcal N)$. It is unique and solves
  $\nabla A(\hat\eta)=\bar T$. In a steep full family this mean domain is
  the interior of the convex support. Boundary empirical means may yield
  only a supremum, as in a Bernoulli sample containing only successes.

* **26. Divergence in an exponential family.** For two interior natural
  parameters,
  $$D(P_\eta\|P_\zeta)
  =A(\zeta)-A(\eta)-\nabla A(\eta)\cdot(\zeta-\eta).$$
  Thus relative entropy is the Bregman divergence of the cumulant function
  with this order of arguments. Its local quadratic term is
  $\tfrac12(\zeta-\eta)^\top\nabla^2A(\eta)(\zeta-\eta)$.

## Reference guide

### Source comparisons and local copies

For the expansion, Schervish's Theorem 5.18 was read for item 19.
Ferguson's Section 4.2 gives the averaging argument: its inequality is for
maximum risk, as now stated in item 7. Berger's normal-mean discussion
supplies the risk-estimation framework of item 20. Item 21 is the block
information inequality, and items 25 and 26 specialize the exponential-family
geometry of Brown and Barndorff-Nielsen. The qualification by steepness
in item 9 distinguishes the mean domain from the entire convex-support
interior. Holm and closed testing extend the simultaneous-inference
material; their error control uses valid marginal and intersection tests,
without independence assumptions.

The third expansion (items 27–39) was checked against the following
passages. Item 27 is Schervish, Section 3.2.4 (the binomial example with
a beta prior). Item 28 follows Berger, Section 6.4 (reduction of scale to
location by logarithms), with the formula checked on the exponential case
and on the scale exercises of Shao's exercise volume. Items 29, 30, and 31
are Schervish, Lemma 4.78, Proposition 4.92 with Lemma 4.96, and
Lemma 4.122 with Definition 4.120; Cox–Hinkley, Section 5.2, gives the same
Neyman-structure argument. Items 32 and 33 are Schervish, Theorem 4.82 and
Theorem 4.100, Section 4.4.2; the limiting point-hypothesis case is his
Theorem 4.104. Item 34 is Schervish, Definition 5.60 and Proposition 5.61,
Ferguson, Section 5.8, and Young–Smith, Section 7.3, which also gives the
expected-length interpretation. Item 35 is Schervish, Theorem 4.68.
Item 36 is Pfanzagl, Proposition 4.4.2 and Example 4.4.5, after Lehmann
and Stein. Items 37 and 38 are Ferguson, Section 5.6 (Theorems 1 and 2, the
listed maximal invariants, and the $t$-test examples with Exercises 5.6.4–
5.6.6), Berger, Section 6.5, and Cox–Hinkley, Section 5.3. Item 39 is
Berger, Section 8.9.2, Theorem 13 and Example 10 (Blyth, 1951).

Ferguson, Chapters 1, 2, 4, and 5, is the course-length source for the
minimax theorem, complete classes, invariance, and testing. Schervish,
Chapters 3–6, develops Bayes rules, admissibility, equivariance, and the
normal-mean problem with the measure theory in place. Cox–Hinkley,
Chapters 4, 5, and 11, treats Neyman structure, unbiased tests, and the
decision-theoretic formulation, including the inadmissibility phenomenon of
item 14. Pfanzagl, Chapters 4 and 5, gives the uniformly most powerful
unbiased tests for exponential families and the passage from those tests to
confidence bounds. Berger is the graduate reference that carries Bayes
rules, minimaxity, invariance, and the James–Stein estimator in one
development. Blackwell and Girshick, and Wald's monograph, are the classical
sources for the game-theoretic theorems and for comparison of experiments.
Brown and Barndorff-Nielsen supply the convex geometry of exponential
families used in items 9 and 10. Kullback is the source for the divergence
in item 11. Miller is the monograph for items 15–17; Scheffé's *Analysis of
Variance* is the source for the simultaneous $F$ bounds.

Lehmann and Casella, *Theory of Point Estimation*, and Lehmann and Romano,
*Testing Statistical Hypotheses*, are not in the local reference directory.
Torgersen's comparison monograph is present as a DjVu file and was not
text-extracted for this pass; item 18 is the finite-parameter theorem shared
by Ferguson and by Blackwell and Girshick. The local Blackwell–Girshick and
Wald scans have no extractable outline; the numbered statements were checked
against Ferguson, Schervish, Cox–Hinkley, and Pfanzagl.

Local texts directly consulted for this selection:

- [Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*](../lean-CKMA/References/Ferguson1967MathematicalStatisticsDecisionTheoreticApproach-AcademicPress.ProbMathStat.pdf).
- [Schervish, *Theory of Statistics*](../lean-CKMA/References/Schervish1995TheoryStatistics-Springer.SSS.pdf).
- [Cox and Hinkley, *Theoretical Statistics*](../lean-CKMA/References/CoxHinkley1974TheoreticalStatistics-ChapmanHallCRC.pdf).
- [Pfanzagl, *Parametric Statistical Theory*](../lean-CKMA/References/Pfanzagl1994ParametricStatisticalTheory-DeGruyter.Textbook.pdf).
- [Berger, *Statistical Decision Theory and Bayesian Analysis*](../lean-CKMA/References/Berger1985StatisticalDecisionTheoryBayesianAnalysis2ndEd-Springer.SSS.pdf).
- [Brown, *Fundamentals of Statistical Exponential Families*](../lean-CKMA/References/Brown1986FundamentalsStatisticalExponentialFamiliesApplicationsStatisticalDecisionTheory-IMS.LNMS9.pdf).
- [Barndorff-Nielsen, *Information and Exponential Families*](../lean-CKMA/References/BarndorffNielsen1978rep2014InformationExponentialFamiliesStatisticalTheory-WileySerProbStat.pdf).
- [Kullback, *Information Theory and Statistics*](../lean-CKMA/References/Kullback1978InformationTheoryStatistics-PeterSmith.pdf).
- [Miller, *Simultaneous Statistical Inference*](../lean-CKMA/References/Miller1981SimultaneousStatisticalInference2ndEd-Springer.SSS.pdf).
- [Scheffé, *The Analysis of Variance*](../lean-CKMA/References/Scheffé1959AnalysisVariance-Wiley.pdf).
- [Blackwell and Girshick, *Theory of Games and Statistical Decisions*](../lean-CKMA/References/BlackwellGirshick1979TheoryGamesStatisticalDecisions-Dover.pdf).
- [Wald, *Statistical Decision Functions*](../lean-CKMA/References/Wald1950StatisticalDecisionFunctions-Wiley.pdf).
- [Young and Smith, *Essentials of Statistical Inference*](../lean-CKMA/References/YoungSmith2005EssentialsStatisticalInference-Cambridge.SerStatProbMath.pdf).
- [Shao, *Mathematical Statistics: Exercises and Solutions*](../lean-CKMA/References/Shao2005MathematicalStatisticsExercisesSolutions-Springer.pdf).
