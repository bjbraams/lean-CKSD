# Synopsis: Bayesian statistics and Monte Carlo methods

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-105).

This synopsis follows Section 105. Subdivision 105A is parametric Bayesian
theory. Subdivision 105B is nonparametric priors, posterior contraction, and
inverse problems. Subdivision 105C is Monte Carlo and Markov chain Monte
Carlo. De Finetti's theorem is
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 55. Bayes rules for a
specified loss are [SYNOPSIS102](SYNOPSIS102.md), item 2. Geometric
ergodicity of a Markov chain is
[CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), item 69. Langevin algorithms
and diffusion-based sampling are in Section 112, and the construction of
variational families is in Section 113. Gaussian-process regression
posteriors are [SYNOPSIS113](SYNOPSIS113.md), item 30, and kriging is
[SYNOPSIS108](SYNOPSIS108.md), items 18 and 31.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-105a"></a>

## 105A. Foundations and Parametric Bayesian Theory

Let the observations be independent with common density $f(x\mid\theta)$
relative to a dominating measure, and let the prior distribution $\Pi$ have
density $\pi$ relative to a measure on the parameter space. The **marginal
density** of the sample $y$ is $m(y)=\int f(y\mid\theta)\,\pi(\theta)\,d\theta$,
and the **posterior density** is $\pi(\theta\mid y)=f(y\mid\theta)\pi(\theta)/m(y)$
wherever $m(y)>0$.

* **1. Bernstein–von Mises theorem.** Let the experiment be locally
  asymptotically normal through independent sampling from a model
  differentiable in quadratic mean at an interior $\theta_0\in\mathbb R^k$,
  with nonsingular Fisher information $I(\theta_0)$. Assume a prior density
  continuous and positive at $\theta_0$ and, for each $\delta>0$, tests
  with both type I error and the supremum type II error over
  $\|\theta-\theta_0\|\ge\delta$ tending to zero. Let $\hat\theta_n$ be
  efficient, with
  $\sqrt n(\hat\theta_n-\theta_0)=I(\theta_0)^{-1}
  n^{-1/2}\sum_i\dot\ell_{\theta_0}(X_i)+o_P(1)$. Then the posterior law of
  $\sqrt n\,(\theta-\hat\theta_n)$ converges in total variation to
  $N(0,I(\theta_0)^{-1})$, in $P_{\theta_0}$-probability. Posterior credible
  balls of a fixed credibility level are therefore asymptotic confidence sets
  of the same level.

A regular exponential family in the natural parameter $\eta$ has density
$h(x)\exp(\eta\cdot T(x)-A(\eta))$ on the natural parameter space.

* **2. Conjugate updating.** A prior with density proportional to
  $\exp(\eta\cdot\chi_0-\nu_0 A(\eta))$, for $\nu_0>0$ and $\chi_0/\nu_0$ in
  the interior of the mean domain, is conjugate for this family. After
  $n$ independent observations the posterior belongs to the same family, with
  parameters $\chi_0+\sum_{i=1}^n T(X_i)$ and $\nu_0+n$.

* **3. Jeffreys prior.** On a regular parametric model of dimension $k$, the
  Jeffreys prior has density proportional to $(\det I(\theta))^{1/2}$ with
  respect to Lebesgue measure, wherever the Fisher information is positive
  definite and continuous. If $\eta=g(\theta)$ is a smooth reparameterization
  with nonsingular derivative, the Jeffreys density computed in the
  $\eta$-coordinate is the image of the Jeffreys density computed in the
  $\theta$-coordinate.

* **4. Normal sampling model.** Let $X_1,\ldots,X_n$ be independent
  $N(\mu,\sigma^2)$. If $\sigma^2$ is known and the prior is
  $\mu\sim N(\mu_0,\tau^2)$, the posterior of $\mu$ is normal, with precision
  $\tau^{-2}+n\sigma^{-2}$ and with mean equal to the precision-weighted
  average of $\mu_0$ and $\bar X$. If $\sigma^2$ is unknown and the prior
  density of $(\mu,\sigma^2)$ is proportional to $1/\sigma^2$, the marginal
  posterior of $\mu$ is a Student $t$ law on $n-1$ degrees of freedom,
  centered at $\bar X$, with scale $s/\sqrt n$, where
  $s^2=\sum_{i=1}^n(X_i-\bar X)^2/(n-1)$, provided $n\ge2$ and
  $s^2>0$, which ensure posterior propriety.

* **5. Laplace approximation and the BIC.** Let the model dimension be $k$,
  let the prior density be continuous and positive at an interior maximum
  likelihood estimator $\hat\theta_n$, and let the observed information
  $J_n=-D^2\ell_n(\hat\theta_n)$ be positive definite. Assume the
  regular fixed-dimensional local quadratic expansion, $J_n/n$ tending to
  a positive definite limit, and tail control making the integral outside
  the concentrating neighborhood negligible. Then
  $$\log m(y)=\ell_n(\hat\theta_n)+\log\pi(\hat\theta_n)
  +\frac k2\log(2\pi)-\frac12\log\det J_n+o_P(1).$$
  Under the regularity of SYNOPSIS103, item 3, $J_n$ is of exact order $n$,
  so $-2\log m(y)=-2\ell_n(\hat\theta_n)+k\log n+O_P(1)$. The Bayes information
  criterion $-2\ell_n(\hat\theta_n)+k\log n$ therefore tracks $-2\log m(y)$
  up to a tight term. Its model-selection property is recorded in
  SYNOPSIS107, item 4.

### Posterior decisions, prediction, and comparison

* **16. Posterior means and quantiles.** For a real parameter with finite
  posterior second moment, squared-error posterior risk is minimized
  uniquely by its posterior mean, and the minimum is its posterior
  variance. With finite posterior first moment, absolute-error risk is
  minimized by any posterior median. More generally, the check loss
  $\rho_\tau(\theta-a)$ of SYNOPSIS106, item 5, is minimized by a posterior
  $\tau$-quantile. A $(1-\alpha)$ credible set $C(X)$ under a proper prior
  satisfies
  $$\int P_\theta(\theta\in C(X))\,\Pi(d\theta)=1-\alpha$$
  if its posterior content is exactly $1-\alpha$ almost surely.
  This is prior-averaged coverage; pointwise asymptotic coverage follows
  under item 1 for the usual regular credible balls.

* **17. Elementary conjugate families.** For $S\sim\mathop{\mathrm{Bin}}(n,p)$
  and a $\mathop{\mathrm{Beta}}(a,b)$ prior, $a,b>0$, the posterior is
  $\mathop{\mathrm{Beta}}(a+S,b+n-S)$ and the next Bernoulli success
  probability is $(a+S)/(a+b+n)$. For independent Poisson observations of
  mean $\lambda$ and a gamma prior with shape $a$ and rate $b$, the
  posterior has shape $a+\sum_iX_i$ and rate $b+n$. For multinomial counts
  and a Dirichlet prior with positive parameters $a_j$, the posterior
  parameters are $a_j+N_j$ and predictive probabilities are
  $(a_j+N_j)/(\sum_\ell a_\ell+n)$. These are finite-dimensional instances
  of the updating rule in item 6.

* **18. Posterior predictive distribution.** For a future observation
  $Y^\star$ conditionally independent of the data given $\theta$,
  $$P(Y^\star\in B\mid X)=\int P_\theta(Y^\star\in B)\,\Pi(d\theta\mid X).$$
  If $\mu(\theta)=\mathbb E_\theta Y^\star$ and
  $v(\theta)=\mathop{\mathrm{Var}}_\theta Y^\star$ have the needed moments,
  $$\mathop{\mathrm{Var}}(Y^\star\mid X)
  =\mathbb E[v(\theta)\mid X]
  +\mathop{\mathrm{Var}}(\mu(\theta)\mid X).$$
  Under normal sampling with the improper prior of item 4 and a proper
  posterior, $(Y^\star-\bar X)/(s\sqrt{1+1/n})$ has posterior predictive
  law $t_{n-1}$. Parameter uncertainty and future observation noise both
  contribute to predictive uncertainty.

* **19. Bayes factors.** Let models $M_0,M_1$ have positive prior
  probabilities and proper within-model priors, with finite positive
  marginal densities $m_0(x),m_1(x)$. Then
  $$\frac{P(M_1\mid x)}{P(M_0\mid x)}
  =\frac{m_1(x)}{m_0(x)}\frac{P(M_1)}{P(M_0)}.$$
  The ratio $m_1/m_0$ is the Bayes factor. Under $0$–$1$ model-selection
  loss the posterior-preferred model is the Bayes decision. An arbitrary
  multiplicative constant in an improper within-model prior generally
  prevents the marginal-likelihood ratio from being defined.

### Credible regions, point nulls, and hierarchical shrinkage

Suppose the posterior has density $\pi(\theta\mid x)$ with respect to
Lebesgue measure on $\mathbb R^k$. A set $C$ is a **highest posterior
density region** of level $1-\alpha$ when
$\{\theta:\pi(\theta\mid x)>k_\alpha\}\subset C\subset
\{\theta:\pi(\theta\mid x)\ge k_\alpha\}$, where $k_\alpha$ is the largest
constant for which $C$ has posterior content at least $1-\alpha$.

* **22. Highest posterior density regions.** Let $C$ be a highest
  posterior density region with posterior content exactly $1-\alpha$ and
  with $k_\alpha>0$. Then $C$ has the smallest Lebesgue volume among all
  measurable sets of posterior content at least $1-\alpha$. For a
  unimodal posterior density on the line that is symmetric about its mode,
  $C$ is the equal-tailed credible interval. The construction is not
  invariant under nonlinear reparameterization: the image of a highest
  posterior density region under a smooth bijection is in general not a
  highest posterior density region for the image posterior. In the model
  $X\sim N(\theta,\sigma^2)$ with $\sigma$ known and the flat prior, the
  region is $[X-z_{\alpha/2}\sigma,\,X+z_{\alpha/2}\sigma]$, which is also
  the exact confidence interval of level $1-\alpha$.

* **23. Point-null Bayes factor and Lindley's paradox.** Let
  $\bar X\sim N(\theta,\sigma^2/n)$ with $\sigma$ known, and test
  $H_0:\theta=\theta_0$ against $H_1:\theta\ne\theta_0$, with
  $\theta\sim N(\theta_0,\tau^2)$ under $H_1$, $\tau>0$. Put
  $z=\sqrt n\,|\bar X-\theta_0|/\sigma$. The Bayes factor of $H_0$ to $H_1$
  is
  $$B_{01}=\Bigl(1+\frac{n\tau^2}{\sigma^2}\Bigr)^{1/2}
  \exp\Bigl(-\frac{z^2}{2}\Bigl(1+\frac{\sigma^2}{n\tau^2}\Bigr)^{-1}\Bigr).$$
  For fixed $z$, and hence fixed $p$-value, $B_{01}\to\infty$ as
  $n\to\infty$ or as $\tau\to\infty$, so the posterior probability of
  $H_0$ tends to $1$ for any fixed positive prior probability of $H_0$.
  Under $H_0$, $B_{01}\to\infty$ in probability; under a fixed
  $\theta\ne\theta_0$, $B_{01}\to0$ almost surely. Over all priors $g_1$
  on $\{\theta\ne\theta_0\}$,
  $$B_{01}\ge\frac{f(x\mid\theta_0)}{\sup_{\theta\ne\theta_0}f(x\mid\theta)},$$
  which equals $\exp(-z^2/2)$ in this normal model.

* **24. Hierarchical normal model.** Let $y_j\mid\theta_j\sim
  N(\theta_j,\sigma_j^2)$ be independent for $j=1,\ldots,J$, with known
  $\sigma_j>0$; let $\theta_j\mid\mu,\tau$ be independent $N(\mu,\tau^2)$;
  and let the hyperprior be $p(\mu,\tau)=p(\tau)$, flat in $\mu$. Then,
  given $(\mu,\tau)$ and $y$, the $\theta_j$ are independent normal with
  $$\hat\theta_j=\frac{y_j/\sigma_j^2+\mu/\tau^2}
  {1/\sigma_j^2+1/\tau^2},\qquad
  V_j=\frac1{1/\sigma_j^2+1/\tau^2}.$$
  Marginally $y_j\mid\mu,\tau\sim N(\mu,\sigma_j^2+\tau^2)$ independently,
  and $\mu\mid\tau,y\sim N(\hat\mu,V_\mu)$ with
  $V_\mu^{-1}=\sum_j(\sigma_j^2+\tau^2)^{-1}$ and
  $\hat\mu=V_\mu\sum_j y_j/(\sigma_j^2+\tau^2)$. Finally
  $$p(\tau\mid y)\propto p(\tau)\,V_\mu^{1/2}
  \prod_{j=1}^J(\sigma_j^2+\tau^2)^{-1/2}
  \exp\Bigl(-\frac{(y_j-\hat\mu)^2}{2(\sigma_j^2+\tau^2)}\Bigr).$$
  With $p(\tau)\propto1$ on $(0,\infty)$ the joint posterior is proper if
  and only if $J\ge3$; with $p(\tau)\propto1/\tau$ it is improper for
  every $J$.

* **25. Empirical Bayes form of the James–Stein estimator.** Let
  $X\sim N_p(\theta,I_p)$ and let the $\theta_i$ be independent
  $N(0,\tau^2)$. The posterior mean is $(1-B)X$ with
  $B=1/(1+\tau^2)$, and marginally $X\sim N_p(0,(1+\tau^2)I_p)$. For
  $p\ge3$, $(p-2)/\|X\|^2$ is unbiased for $B$ under this marginal law,
  and substituting it gives the James–Stein estimator of SYNOPSIS102,
  item 14. Substituting instead the marginal maximum likelihood estimator
  of $\tau^2$, truncated at zero, gives
  $(1-p/\|X\|^2)_+X$. If the common prior mean $\mu$ is also unknown and
  $S=\sum_i(X_i-\bar X)^2$, then for $p\ge4$ the quantity $(p-3)/S$ is
  unbiased for $B$, giving the Efron–Morris estimator
  $\bar X+(1-(p-3)/S)(X_i-\bar X)$, which shrinks toward the grand mean.

* **26. Tweedie's formula and Robbins' estimator.** Let
  $f(x\mid\theta)=h(x)\exp(\theta\cdot x-\psi(\theta))$ be a density on
  $\mathbb R^k$ with respect to Lebesgue measure, let the prior $g$ be
  arbitrary, and let $m$ be the marginal density, assumed positive and
  differentiable under the integral sign. Then
  $$\mathbb E[\theta\mid X=x]=\nabla\log m(x)-\nabla\log h(x).$$
  The Gaussian case is SYNOPSIS112, item 21. For Poisson sampling,
  $X\mid\theta\sim\mathop{\mathrm{Poi}}(\theta)$ with any prior on
  $(0,\infty)$, the posterior mean is
  $$\mathbb E[\theta\mid X=x]=(x+1)\frac{m(x+1)}{m(x)},$$
  where $m$ is the marginal probability mass function. Robbins'
  nonparametric empirical Bayes estimator replaces $m$ by the empirical
  frequencies of independent observations $X_1,\ldots,X_n$ drawn from
  $m$, with no parametric form assumed for the prior.

<a id="synopsis-105b"></a>

## 105B. Nonparametric Bayes, Posterior Asymptotics, and Inverse Problems

Let $\mathcal X$ be a standard Borel space and let $\alpha$ be a finite
nonzero measure on $\mathcal X$. Write $|\alpha|=\alpha(\mathcal X)$ and
$H=\alpha/|\alpha|$.

* **6. Dirichlet process.** A random probability measure $P$ is a Dirichlet
  process with parameter $\alpha$ when, for every finite measurable partition
  $A_1,\ldots,A_k$,
  $$(P(A_1),\ldots,P(A_k))\sim\mathop{\mathrm{Dirichlet}}(\alpha(A_1),\ldots,\alpha(A_k)).$$
  Conditionally on $P$, let $X_1,\ldots,X_n$ be independent with law $P$. The
  posterior of $P$ is a Dirichlet process with parameter
  $\alpha+\sum_{i=1}^n\delta_{X_i}$. The one-step predictive distribution is
  $$\frac{\alpha+\sum_{i=1}^n\delta_{X_i}}{|\alpha|+n}.$$
  In the Sethuraman representation, let $V_k$ be independent
  $\mathop{\mathrm{Beta}}(1,|\alpha|)$ and let $\theta_k$ be independent with
  law $H$, independent of the $V_k$. The weights
  $\pi_k=V_k\prod_{j<k}(1-V_j)$ give
  $\sum_{k\ge1}\pi_k\delta_{\theta_k}$ the law of a Dirichlet process with
  parameter $\alpha$.

* **27. Pólya urn scheme and distinct values.** If $X_1,X_2,\ldots$ are
  conditionally independent with law $P$ given a Dirichlet process
  $P$ with parameter $\alpha$, then $X_1\sim H$ and
  $$X_{n+1}\mid X_1,\ldots,X_n\sim
  \frac{\alpha+\sum_{i=1}^n\delta_{X_i}}{|\alpha|+n},$$
  the generalized Pólya urn of Blackwell and MacQueen. Conversely, a
  sequence with these predictive laws is exchangeable, and the random
  measure given by de Finetti's theorem (CKMA SYNOPSIS06, item 55) is a
  Dirichlet process with parameter $\alpha$. If $\alpha$ is atomless, the
  indicators that $X_i$ is a new value are independent Bernoulli variables
  with success probabilities $|\alpha|/(|\alpha|+i-1)$. Hence the number
  $K_n$ of distinct values among $X_1,\ldots,X_n$ satisfies
  $$\mathbb EK_n=\sum_{i=1}^n\frac{|\alpha|}{|\alpha|+i-1}
  \sim|\alpha|\log n,\qquad \frac{K_n}{\log n}\to|\alpha|
  \quad\text{almost surely}.$$

* **7. Doob's consistency theorem.** Consider a dominated model
  $\{P_\theta:\theta\in\Theta\}$ on a standard Borel sample space, with
  $\Theta$ Polish with its Borel $\sigma$-field, and a prior $\Pi$ on
  $\Theta$. Assume the family is measurably parameterized. If
  $\theta\mapsto P_\theta$ is injective, then there is a $\Pi$-null set $N$ such that for every
  $\theta\notin N$ and every neighborhood $U$ of $\theta$, the posterior
  probability of $U$ tends to $1$, $P_\theta$-almost surely.

* **8. Schwartz's theorem.** Let $P_0$ have density $p_0$, and write
  $K(P_0,P)=\int p_0\log(p_0/p)$ for the Kullback–Leibler divergence. Suppose
  that the prior gives positive mass to
  $\{P:K(P_0,P)<\varepsilon\}$ for every $\varepsilon>0$. Suppose that for
  every weak neighborhood $U$ of $P_0$ there exist tests of $P_0$ against
  $U^c$ whose type I and type II errors both tend to zero, uniformly over
  $U^c$. Then the posterior probability of $U$ tends to $1$ in
  $P_0$-probability.

For a probability $P$ with density $p$, write
$V(P_0,P)=\int p_0\bigl(\log(p_0/p)\bigr)^2$ and write $h$ for Hellinger
distance, normalized by $h^2(P,Q)=\int(\sqrt p-\sqrt q)^2$.
Let $N(\varepsilon,\mathcal F,h)$ be the covering number of
$\mathcal F$ in that distance.

* **9. Contraction rate of Ghosal, Ghosh, and van der Vaart.** Let
  $\varepsilon_n\to0$ with $n\varepsilon_n^2\to\infty$. Suppose that for some
  finite $C$,
  $$\Pi\bigl(\{P:K(P_0,P)\le\varepsilon_n^2,\;
  V(P_0,P)\le\varepsilon_n^2\}\bigr)
  \ge\exp(-Cn\varepsilon_n^2),$$
  and that there exist sieves $\mathcal F_n$ with
  $\log N(\varepsilon_n/2,\mathcal F_n,h)\le n\varepsilon_n^2$ and
  $$\Pi(\mathcal F_n^c)\le\exp(-(C+4)n\varepsilon_n^2).$$
  Then there exists $M_0<\infty$ such that for every $M\ge M_0$ the posterior
  probability of $\{P:h(P,P_0)\ge M\varepsilon_n\}$ tends to zero in
  $P_0$-probability.

* **10. Linear inverse problems.** In the white-noise model
  $dY=Af\,dt+\varepsilon\,dW$ on a bounded domain, suppose that $A$ is compact
  and injective with singular values of order $j^{-a}$, $a\ge0$, and that the
  unknown function lies in a Sobolev ellipsoid of smoothness $\beta>0$
  in the right singular-vector basis of $A$, so that its smoothness and
  the singular-value decay are aligned. The minimax rate for the $L^2$
  estimation error is of order $\varepsilon^{2\beta/(2\beta+2a+1)}$.
  Independent centered Gaussian prior coefficients with variances of
  order $j^{-1-2\beta}$ yield posterior contraction at this rate,
  uniformly over a fixed such ball. Fixing a different prior smoothness
  generally worsens this uniform rate, although individual smoother
  truths can have faster contraction.

<a id="synopsis-105c"></a>

## 105C. Monte Carlo and Bayesian Computation

* **11. Importance sampling.** Let the target probability have density $p$ and
  let the proposal have density $q$, with $p$ absolutely continuous with
  respect to $q$. If $\mathbb E_q[(p/q)|h|]<\infty$, then
  $\mathbb E_p h=\mathbb E_q[(p/q)h]$. For an independent sample from $q$, the
  average of $(p/q)(X_i)h(X_i)$ is unbiased for $\mathbb E_p h$, with variance
  $n^{-1}\bigl(\mathbb E_q[(p/q)^2h^2]-(\mathbb E_p h)^2\bigr)$. The
  self-normalized weights $w_i/\sum_j w_j$, with $w_i=p(X_i)/q(X_i)$, are
  consistent for $\mathbb E_p h$ whenever $\mathbb E_q[(p/q)|h|]<\infty$.

Let $\pi$ be a target density on a measurable space and let $q(x,dy)$ be a
proposal kernel that admits a density $q(x,y)$ in the second variable.

* **12. Metropolis–Hastings.** Define the acceptance probability
  $$\alpha(x,y)=\min\Bigl(1,
  \frac{\pi(y)q(y,x)}{\pi(x)q(x,y)}\Bigr)$$
  when the denominator is positive, and $\alpha(x,y)=1$ when
  $\pi(x)q(x,y)=0$. The kernel that proposes $Y\sim q(x,\cdot)$ and moves
  from $x$ to $Y$ with probability $\alpha(x,Y)$, remaining at $x$ otherwise,
  is reversible with respect to $\pi$ and therefore leaves $\pi$ invariant.

* **13. Gibbs sampling.** Suppose the joint distribution is absolutely
  continuous with respect to a product measure and its density is positive on
  the product of the coordinate supports. The kernel that updates one
  coordinate from its conditional distribution given the others, in a
  deterministic or a random scan, leaves the joint distribution invariant.

* **14. Central limit theorem for Markov chain Monte Carlo.** Let
  $(X_t)_{t\ge0}$ be a Markov chain with invariant probability $\pi$,
  satisfying the drift and minorization condition of CKMA SYNOPSIS08,
  item 69. If $f$ is measurable and $\mathbb E_\pi|f|^{2+\delta}<\infty$ for
  some $\delta>0$, then
  $$\sqrt n\Bigl(n^{-1}\sum_{t=1}^n f(X_t)-\pi(f)\Bigr)
  \Rightarrow N(0,\sigma^2(f)),$$
  where
  $$\sigma^2(f)=\mathop{\mathrm{Var}}_\pi(f(X_0))
  +2\sum_{k=1}^\infty\mathop{\mathrm{Cov}}_\pi\bigl(f(X_0),f(X_k)\bigr)$$
  and the series converges absolutely.

For a density $q$ on the parameter, the **evidence lower bound** of a sample
$y$ is $\mathbb E_q\log p(y,\theta)-\mathbb E_q\log q(\theta)$.

* **15. Evidence lower bound.** For every probability $q$ absolutely
  continuous with respect to the posterior,
  $$\log p(y)=\mathbb E_q\log p(y,\theta)-\mathbb E_q\log q(\theta)
  +\mathop{\mathrm{KL}}(q\,\|\,p(\cdot\mid y)).$$
  Maximizing the evidence lower bound over a family of densities $q$ is
  therefore the same as minimizing the Kullback–Leibler divergence from $q$
  to the posterior. A mean-field family restricts $q$ to a product of
  coordinate laws. The construction of such families is in Section 113.

* **20. Self-normalized importance-sampling limit.** In item 11, put
  $w=p/q$, $\mu=\mathbb E_p h$, and suppose
  $\mathbb E_q[w^2(h-\mu)^2]<\infty$ and $\mathbb E_q[w|h|]<\infty$.
  For independent proposal draws,
  $$\sqrt n\left(\frac{\sum_iw(X_i)h(X_i)}{\sum_iw(X_i)}-\mu\right)
  \Rightarrow N\left(0,\mathbb E_q[w^2(h-\mu)^2]\right).$$
  Multiplying all weights by a common unknown constant leaves the estimator
  unchanged. The asymptotic variance can be much larger than
  $\mathop{\mathrm{Var}}_p h$ when the proposal poorly covers the target.

* **21. Conditional Monte Carlo.** If $(U_i,V_i)$ are independent copies
  and $H(U,V)\in L^2$, replacing $H(U_i,V_i)$ by
  $\mathbb E[H(U_i,V_i)\mid U_i]$ in a Monte Carlo average preserves its
  expectation and decreases its variance. This is the conditional-expectation
  argument behind Rao–Blackwellization, without a statistical sufficiency
  requirement. For a serial Markov chain, a decrease in one-step variance
  alone does not compare the full asymptotic variances of item 14.

### Exact simulation and variance reduction

For a distribution function $F$ on $\mathbb R$, the **generalized inverse**
is $F^-(u)=\inf\{x:F(x)\ge u\}$ for $u\in(0,1)$.

* **28. Inverse-transform sampling.** If $U$ is uniform on $(0,1)$, then
  $F^-(U)$ has distribution function $F$, since $F^-(u)\le x$ exactly
  when $u\le F(x)$. If $F$ is continuous and $X\sim F$, then $F(X)$ is
  uniform on $(0,1)$.

* **29. Accept–reject sampling.** Let $f$ and $g$ be probability densities
  with $f\le Mg$ for a constant $M\ge1$. Draw $Y\sim g$ and an independent
  uniform $U$ on $(0,1)$, and accept $Y$ when $U\le f(Y)/(Mg(Y))$;
  otherwise repeat independently. The accepted value has density $f$
  exactly, each trial is accepted with probability $1/M$, and the number
  of trials is geometric with mean $M$. If only an unnormalized
  $\tilde f=Zf$ is known, with $\tilde f\le\tilde Mg$, the same rule with
  $\tilde M$ in place of $M$ still produces exact draws from $f$, with
  acceptance probability $Z/\tilde M$.

* **30. Control and antithetic variates.** Let $Y$ and $C$ be
  square-integrable functions of the same simulation draw, with
  $\mathbb EC$ known and $\mathop{\mathrm{Var}}C>0$. For every $b$, the
  variable $Y-b(C-\mathbb EC)$ has mean $\mathbb EY$; its variance is
  minimized at $b^*=\mathop{\mathrm{Cov}}(Y,C)/\mathop{\mathrm{Var}}C$,
  where it equals $(1-\rho^2)\mathop{\mathrm{Var}}Y$ with $\rho$ the
  correlation of $Y$ and $C$. For antithetic sampling, let $U$ be uniform
  on $(0,1)$ and let $h\in L^2(0,1)$ be monotone. Then
  $\mathop{\mathrm{Cov}}(h(U),h(1-U))\le0$, so the unbiased average
  $\tfrac12(h(U)+h(1-U))$ has variance at most
  $\tfrac12\mathop{\mathrm{Var}}h(U)$, the variance obtained from two
  independent draws.

### Convergence of Markov chain samplers

* **31. Convergence of Metropolis–Hastings.** Suppose the chain of item
  12 is $\pi$-irreducible. Then it is Harris recurrent, and for every
  $h\in L^1(\pi)$ the averages $n^{-1}\sum_{t\le n}h(X_t)$ converge to
  $\pi(h)$ almost surely from every starting point. If it is also
  aperiodic, then $P^n(x,\cdot)\to\pi$ in total variation for every $x$,
  as in CKMA SYNOPSIS08, item 68. Irreducibility holds if $q(x,y)>0$ for
  all $x,y$ in the support of $\pi$, and aperiodicity holds if rejection
  has positive probability. On $\mathbb R^d$, if the support of $\pi$ is
  open and connected, $\pi$ is bounded and bounded away from zero on its
  compact subsets, and $q(x,y)\ge\varepsilon$ whenever
  $|x-y|<\delta$, for some $\varepsilon,\delta>0$, then the chain is
  $\pi$-irreducible and aperiodic and every nonempty compact subset of
  the support is small.

* **32. Independence and random-walk samplers.** In the independence
  sampler, $q(x,y)=g(y)$ for a density $g$. If $\pi\le Mg$ on the support of
  $\pi$, then
  $$\sup_A|P^n(x,A)-\pi(A)|\le(1-1/M)^n$$
  for every $x$, so the chain is uniformly ergodic. If $\pi/g$ is not
  essentially bounded, the chain is not geometrically ergodic. For a
  random-walk sampler on $\mathbb R$, with symmetric positive increment
  density, geometric ergodicity requires
  $\int e^{s|x|}\pi(dx)<\infty$ for some $s>0$. If $\pi$ is symmetric
  and log-concave in the tails, in the sense that
  $\log\pi(x)-\log\pi(y)\ge a|y-x|$ for some $a>0$ and $x_1$ whenever
  $x_1\le x<y$ or $y<x\le-x_1$, the chain is geometrically ergodic.

* **33. Gibbs sampling as Metropolis–Hastings; two-stage samplers.**
  Each coordinate update of item 13 is a Metropolis–Hastings step whose
  proposal is the full conditional law, and its acceptance probability is
  identically $1$. For a two-stage sampler on a pair $(X,Y)$, which
  alternately draws $X$ given $Y$ and $Y$ given $X$, each of the two
  marginal sequences is itself a Markov chain, reversible with respect to
  its stationary marginal. If one marginal chain is ergodic, or
  geometrically ergodic, so is the other. Under stationarity the
  autocovariances $\mathop{\mathrm{Cov}}(h(X^{(0)}),h(X^{(t)}))$ are
  nonnegative and nonincreasing in $t$ for every $h$ with finite
  variance. Moreover, the conditional average
  $T^{-1}\sum_{t\le T}\mathbb E[h(X)\mid Y^{(t)}]$ has variance no
  larger than $T^{-1}\sum_{t\le T}h(X^{(t)})$ for every $T$. In this
  two-stage setting the comparison left open in item 21 is therefore
  resolved in favor of conditioning. When $X$ is a parameter and $Y$ is
  missing data, the scheme is data augmentation.

For a nonnegative integrable function $f_1$ proportional to $\pi$ on
$\mathbb R^d$, the **slice sampler** alternates
$U\mid X=x\sim\mathop{\mathrm{Unif}}(0,f_1(x))$ and
$X\mid U=u\sim\mathop{\mathrm{Unif}}\{x:f_1(x)>u\}$, with the uniform law
taken with respect to Lebesgue measure.

* **34. Slice sampler.** Both steps leave invariant the uniform law on
  $\{(x,u):0<u<f_1(x)\}$, whose first marginal is $\pi$, so the
  $X$-sequence has stationary law $\pi$ and the normalizing constant of
  $f_1$ is never needed. If $f_1$ is bounded and has bounded support, the
  slice sampler is uniformly ergodic.

Let $\pi(x)\propto\exp(-U(x))$ on $\mathbb R^d$ with $U$ continuously
differentiable, let $M$ be positive definite, and put
$H(x,p)=U(x)+\tfrac12p^\top M^{-1}p$. One **leapfrog step** of size
$\varepsilon>0$ maps $(x,p)$ to $(x',p')$ through
$p_{1/2}=p-\tfrac\varepsilon2\nabla U(x)$,
$x'=x+\varepsilon M^{-1}p_{1/2}$, and
$p'=p_{1/2}-\tfrac\varepsilon2\nabla U(x')$. Let $\Phi$ be the composition
of $L$ such steps.

* **35. Hamiltonian Monte Carlo.** The map $\Phi$ preserves Lebesgue
  measure on $\mathbb R^{2d}$ and is reversible:
  $\Phi(x,p)=(x',p')$ implies $\Phi(x',-p')=(x,-p)$. Draw
  $p\sim N(0,M)$, compute $(x',p')=\Phi(x,p)$, and move to $x'$ with
  probability
  $$\min\bigl(1,\exp(H(x,p)-H(x',p'))\bigr),$$
  remaining at $x$ otherwise. This kernel leaves $\pi$ invariant, because
  it is a Metropolis–Hastings step for the joint density proportional to
  $\exp(-H)$ with a measure-preserving involutive proposal, followed by
  momentum refreshment. The exact Hamiltonian flow conserves $H$, so
  rejections arise only from discretization error. Langevin-type
  dynamics are in Section 112.

### Mean-field coordinate ascent

* **36. Coordinate-ascent variational updates.** In item 15, restrict
  $q=\prod_jq_j$ to a product over blocks $\theta=(\theta_1,\ldots,\theta_J)$.
  With the factors $q_\ell$, $\ell\ne j$, held fixed, the evidence lower
  bound is maximized over $q_j$ by
  $$q_j^*(\theta_j)\propto\exp\Bigl(\mathbb E_{q_{-j}}\log p(y,\theta)\Bigr),$$
  provided the right side is integrable, where $\mathbb E_{q_{-j}}$
  averages over the other blocks. Indeed, as a function of $q_j$, the
  evidence lower bound differs from
  $-\mathop{\mathrm{KL}}(q_j\,\|\,q_j^*)$ by a constant. Cycling through
  these updates therefore never decreases the evidence lower bound. The
  mean-field problem is not convex in general, so the limit can be a
  local optimum that depends on the initialization.

## Reference guide

### Correspondence with the subdivisions

- **[105A](#synopsis-105a)**: Jeffreys, Box and Tiao, Berger, Robert, Ghosh,
  Delampady, and Samanta, and Gelman, Carlin, Stern, Dunson, Vehtari, and
  Rubin carry conjugate analysis, invariant priors, the Laplace expansion,
  and the Bernstein–von Mises theorem.
- **[105B](#synopsis-105b)**: Giné and Nickl, and Nickl's Zurich lectures,
  carry posterior contraction and Bayesian inverse problems. The Dirichlet
  process and the general contraction theorem are the theorems of Ferguson,
  Sethuraman, Doob, Schwartz, and Ghosal, Ghosh, and van der Vaart.
- **[105C](#synopsis-105c)**: Robert's computational chapters, Del Moral,
  Douc, Moulines, Priouret, and Soulier, Meyn and Tweedie, and Levin, Peres,
  and Wilmer carry importance sampling and Markov chain Monte Carlo.
  Wainwright and Jordan carry the evidence lower bound. Robert and Casella,
  Liu, and Hammersley and Handscomb carry exact simulation, variance
  reduction, convergence of Metropolis–Hastings and Gibbs samplers, the
  slice sampler, and hybrid Monte Carlo.

### Source comparisons and local copies

Ghosh, Delampady, and Samanta, Sections 2.6–2.8, were consulted for
posterior propriety, posterior loss minimization, Bayes factors, and
prediction. Robert–Casella, Chapters 3–4, supplies importance sampling
and conditional Monte Carlo; its full text is in `ReferencesSuppl`.
For item 1, van der Vaart's Theorem 10.1 gives quadratic-mean
differentiability and uniformly consistent separation tests, rather than
posterior consistency alone. Ghosal–van der Vaart's Theorem 8.9, also
read in a supplemental local copy, supplies the half-radius entropy
condition and the sieve-tail exponent $C+4$ used in item 9.

Item 5 is the Laplace expansion used by Ghosh, Delampady, and Samanta and by
Robert. Item 9 uses a standard sufficient contraction criterion with
sieve-tail exponent $C+4$, consistent with the local Ghosal–van der Vaart
treatment. Items 12 and 13 are the invariance statements of the Monte Carlo
texts. Item 14 invokes the geometric
ergodicity criterion already numbered in the analysis synopsis.

For the third expansion, Berger's Sections 4.3.2–4.3.3 and 4.5.2–4.5.4
were read for highest posterior density sets, the point-null Bayes factor
(4.17) with the lower bound of Theorem 1 in Section 4.3.3, the normal-means
empirical Bayes estimates (4.33)–(4.35), and Robbins' Poisson estimator
(Example 16). Robert's Definition 5.5.2, Lemma 10.4.2, and Examples 10.4.1
and 10.5.1 supply the volume property of highest posterior density
regions, the exponential-family posterior-mean identity, and the empirical
Bayes reading of the James–Stein estimator. Ghosh, Delampady, and Samanta,
Section 6.4, were read for the Jeffreys–Lindley paradox, and Gelman et
al., Section 5.4, equations (5.17)–(5.21), for the hierarchical normal
model; the propriety threshold $J\ge3$ for the flat prior on $\tau$ in item
24 follows from the tail $\tau^{1-J}$ of (5.21). Ghosal–van der Vaart,
Section 4.1.4, Proposition 4.8, and Section 4.2.4 supply item 27. In
Robert–Casella, Lemma 2.4, Corollary 2.17, and Section 4.4.2 were read for
items 28–30, Theorem 7.4, Lemmas 7.3 and 7.6, Theorems 7.8 and 7.15 for
items 31 and 32, Theorems 9.12, 9.19, 10.13, Corollary 9.14, and
Proposition 9.18 for item 33, and Section 8.1 with Lemma 8.5 for item 34.
Hammersley and Handscomb, Sections 5.5–5.6, supply the control and
antithetic constructions. Liu, Sections 9.2–9.3, was read for the leapfrog
integrator and hybrid Monte Carlo. Gelman et al., Section 13.7, and
Wainwright and Jordan, Section 5.3, were read for the mean-field
coordinate update.

Bernardo and Smith, *Bayesian Theory*, DeGroot, *Optimal Statistical
Decisions* were not located locally. Supplemental copies of Ghosh–Ramamoorthi,
Kaipio–Somersalo, Asmussen–Glynn, and Chopin–Papaspiliopoulos are present;
they were located but not read for this expansion. The consulted
supplemental copies of Ghosal–van der Vaart and Robert–Casella are linked
below.

Local texts directly consulted or identified for this selection:

- [Ghosal and van der Vaart, *Fundamentals of Nonparametric Bayesian Inference*](../lean-CKMA/ReferencesSuppl/GhosalVanDerVaart2017FundamentalsNonparametricBayesianInference-CambridgeSerStatProbMath44.pdf).
  Theorem 8.9 was read for the contraction criterion.
- [Robert and Casella, *Monte Carlo Statistical Methods*](../lean-CKMA/ReferencesSuppl/RobertCasella2004MonteCarloStatisticalMethods2ndEd-Springer.pdf).
  Chapters 3–4 were consulted for importance sampling and variance reduction.
- [Liu, *Monte Carlo Strategies in Scientific Computing*](../lean-CKMA/ReferencesSuppl/Liu2004MonteCarloStrategiesScientificComputing-SpringerSerStat.pdf).
  Sections 9.2–9.3 were read for hybrid Monte Carlo.
- [Hammersley and Handscomb, *Monte Carlo Methods*](../lean-CKMA/ReferencesSuppl/HammersleyHandscomb1964MonteCarloMethods-ChapmanHallMonogAPS.pdf).
  Sections 5.5–5.6 were read for control and antithetic variates.
- [van der Vaart, *Asymptotic Statistics*](../lean-CKMA/References/VanDerVaart1998AsymptoticStatistics-CambridgeSerStatProbMath03.pdf).
  Theorem 10.1 was read for the parametric posterior normal limit.
- [Jeffreys, *Theory of Probability*](../lean-CKMA/References/Jeffreys1998TheoryProbability3rdEd-OxfordUP.ClassicTextsPhysSci.pdf).
- [Savage, *The Foundations of Statistics*](../lean-CKMA/References/Savage1972FoundationsStatistics2ndRevEd-Dover.pdf).
- [Box and Tiao, *Bayesian Inference in Statistical Analysis*](../lean-CKMA/References/BoxTiao1973BayesianInferenceStatisticalAnalysis-AddisonWesley.pdf).
- [Berger, *Statistical Decision Theory and Bayesian Analysis*](../lean-CKMA/References/Berger1985StatisticalDecisionTheoryBayesianAnalysis2ndEd-Springer.SSS.pdf).
- [Ghosh, Delampady, and Samanta, *An Introduction to Bayesian Analysis*](../lean-CKMA/References/GhoshDelampadySamanta2006IntroductionBayesianAnalysisTheoryMethods-SpringerSTS.pdf).
- [Robert, *The Bayesian Choice*](../lean-CKMA/References/Robert2007BayesianChoiceDecisionTheoreticFoundationsComputationalImplementation2ndEd-Springer.STS.pdf).
- [Gelman, Carlin, Stern, Dunson, Vehtari, and Rubin, *Bayesian Data Analysis*](../lean-CKMA/References/GelmanEtAl2014BayesianDataAnalysis3rdEd-ChapmanHallCRC.TextsStatSci.pdf).
- [Giné and Nickl, *Mathematical Foundations of Infinite-Dimensional Statistical Models*](../lean-CKMA/References/GinéNickl2015MathematicalFoundationsInfiniteDimensionalStatisticalModels-CambridgeSerStatProbMath40.pdf).
- [Nickl, *Bayesian Non-linear Statistical Inverse Problems*](../lean-CKMA/References/Nickl2023BayesianNonlinearStatisticalInverseProblems-EMS.ZLAM30.pdf).
- [Del Moral, *Mean Field Simulation for Monte Carlo Integration*](../lean-CKMA/References/DelMoral2013MeanFieldSimulationMonteCarloIntegration-ChapmanHallCRC.MSAP126.pdf).
- [Douc, Moulines, Priouret, and Soulier, *Markov Chains*](../lean-CKMA/References/DoucMoulinesPriouretSoulier2018MarkovChains-Springer.SSORFE.pdf).
- [Meyn and Tweedie, *Markov Chains and Stochastic Stability*](../lean-CKMA/References/MeynTweedie2009MarkovChainsStochasticStability-CambridgeMathLibrary.pdf).
- [Levin, Peres, and Wilmer, *Markov Chains and Mixing Times*](../lean-CKMA/References/LevinPeres2017MarkovChainsMixingTimes2ndEd-AMS.pdf).
- [Wainwright and Jordan, *Graphical Models, Exponential Families, and Variational Inference*](../lean-CKMA/References/WainwrightJordan2008GraphicalModelsExponentialFamiliesVariationalInference-NowPublishers.FnTML1.pdf).
