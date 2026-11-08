# Synopsis: Bayesian inference and stochastic computation

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-104).

This synopsis follows Section 104. Subdivision 104A is parametric
Bayesian theory, nonparametric priors, posterior contraction, and inverse
problems. Subdivision 104B is Monte Carlo and Markov chain Monte Carlo,
followed by the continuous-time sampling dynamics of Langevin type,
stochastic approximation, interacting particle systems, filtering, and
mean-field training. Subdivision 104C is score-based generation and
Schrödinger bridges. De Finetti's theorem is
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 55. Bayes rules for a
specified loss are [SYNOPSIS101](SYNOPSIS101.md), item 33. Geometric ergodicity of a Markov chain, Girsanov's
theorem, and the Feynman–Kac formula are
[CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), items 69, 29, and 36. The
Wasserstein gradient flow of free energy, the contraction of $\mathrm{EVI}$
flows, and entropic transport are
[CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md), items 62, 59, and 90.
Poincaré and logarithmic Sobolev inequalities, with the Bakry–Émery
criterion, are [CKMA SYNOPSIS14](../lean-CKMA/SYNOPSIS14.md), items 34–38
and 47–48. Gaussian-process regression posteriors are [SYNOPSIS107](SYNOPSIS107.md), item 34; kriging and
the Kalman filter are [SYNOPSIS106](SYNOPSIS106.md), items 7, 20, and 23. Mean-field games remain in CKMA
Section 8.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-104a"></a>

## 104A. Foundations, Parametric Bayesian Theory, and Nonparametric Bayes

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
  $N(0,I(\theta_0)^{-1})$, in $P_{\theta_0}$-probability. Consequently, if
  $C_n$ is the closed Euclidean ball centered at $\hat\theta_n$ of posterior
  content $1-\alpha$, with $0<\alpha<1$, then
  $P_{\theta_0}(\theta_0\in C_n)\to1-\alpha$.

A regular exponential family in the natural parameter $\eta$ has density
$h(x)\exp(\eta\cdot T(x)-A(\eta))$ on the natural parameter space.

* **2. Conjugate updating.** A prior with density proportional to
  $\exp(\eta\cdot\chi_0-\nu_0 A(\eta))$, for $\nu_0>0$ and $\chi_0/\nu_0$ in
  the interior of the convex hull of the support of $T(X)$, is a proper
  prior and is conjugate for this family. After
  $n$ independent observations the posterior belongs to the same family, with
  parameters $\chi_0+\sum_{i=1}^n T(X_i)$ and $\nu_0+n$.

* **3. Jeffreys prior.** Let a model on an open set
  $\Theta\subset\mathbb R^k$ have log-density differentiable in $\theta$,
  with square-integrable score and positive definite Fisher information
  $I(\theta)$. The Jeffreys prior is the measure with Lebesgue density
  $(\det I(\theta))^{1/2}$. If $g:\Theta\to g(\Theta)$ is a continuously
  differentiable bijection with nonsingular derivative and $\eta=g(\theta)$,
  the Fisher information in $\eta$ is
  $I^g(\eta)=Dg^{-1}(\eta)^\top I(g^{-1}(\eta))\,Dg^{-1}(\eta)$. Hence
  $(\det I^g(\eta))^{1/2}=(\det I(g^{-1}(\eta)))^{1/2}|\det Dg^{-1}(\eta)|$,
  so the Jeffreys measure in $\eta$ is the image under $g$ of the Jeffreys
  measure in $\theta$.

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

* **5. Laplace approximation and the BIC.** Let $\Theta\subset\mathbb R^k$
  be open, let $y=(X_1,\ldots,X_n)$ be independent with density
  $f(\cdot\mid\theta_0)$, $\theta_0\in\Theta$, let
  $\ell_n(\theta)=\sum_i\log f(X_i\mid\theta)$ be twice continuously
  differentiable, and let the prior be a probability with density $\pi$
  continuous and positive at $\theta_0$. Suppose that, with probability
  tending to one, $\ell_n$ has a maximizer $\hat\theta_n$, and that
  $\hat\theta_n\to\theta_0$ in probability. Suppose there are $\delta>0$ and
  a positive definite matrix $J$ with
  $\sup_{\|\theta-\theta_0\|\le\delta}\|n^{-1}D^2\ell_n(\theta)+J\|\to0$ in
  probability, and that for every $\varepsilon>0$ there is $\eta>0$ with
  $P\bigl(\sup_{\|\theta-\hat\theta_n\|\ge\varepsilon}
  (\ell_n(\theta)-\ell_n(\hat\theta_n))\le-n\eta\bigr)\to1$. Put
  $J_n=-D^2\ell_n(\hat\theta_n)$. Then
  $$\log m(y)=\ell_n(\hat\theta_n)+\log\pi(\hat\theta_n)
  +\frac k2\log(2\pi)-\frac12\log\det J_n+o_P(1).$$
  Since $J_n/n\to J$ in probability,
  $-2\log m(y)=-2\ell_n(\hat\theta_n)+k\log n+O_P(1)$. The quantity
  $-2\ell_n(\hat\theta_n)+k\log n$ is the Bayes information criterion; its
  consistency for nested Gaussian regression models with known variance is
  SYNOPSIS103, item 36.

### Posterior decisions, prediction, and comparison

* **6. Posterior means and quantiles.** For a real parameter with finite
  posterior second moment, squared-error posterior risk is minimized
  uniquely by its posterior mean, and the minimum is its posterior
  variance. With finite posterior first moment, absolute-error risk is
  minimized by any posterior median. More generally, the check loss
  $\rho_\tau(\theta-a)$ of SYNOPSIS105, item 5, is minimized by a posterior
  $\tau$-quantile. A $(1-\alpha)$ credible set $C(X)$ under a proper prior
  satisfies
  $$\int P_\theta(\theta\in C(X))\,\Pi(d\theta)=1-\alpha$$
  if its posterior content is exactly $1-\alpha$ almost surely.
  This is prior-averaged coverage; pointwise asymptotic coverage of
  credible balls is the last statement of item 1.

* **7. Elementary conjugate families.** For $S\sim\mathop{\mathrm{Bin}}(n,p)$
  and a $\mathop{\mathrm{Beta}}(a,b)$ prior, $a,b>0$, the posterior is
  $\mathop{\mathrm{Beta}}(a+S,b+n-S)$ and the next Bernoulli success
  probability is $(a+S)/(a+b+n)$. For independent Poisson observations of
  mean $\lambda$ and a gamma prior with shape $a$ and rate $b$, the
  posterior has shape $a+\sum_iX_i$ and rate $b+n$. For multinomial counts
  and a Dirichlet prior with positive parameters $a_j$, the posterior
  parameters are $a_j+N_j$ and predictive probabilities are
  $(a_j+N_j)/(\sum_\ell a_\ell+n)$. These are finite-dimensional instances
  of the updating rule in item 15.

* **8. Posterior predictive distribution.** For a future observation
  $Y^\star$ conditionally independent of the data given $\theta$,
  $$P(Y^\star\in B\mid X)=\int P_\theta(Y^\star\in B)\,\Pi(d\theta\mid X).$$
  If $Y^\star$ is real and
  $\int\mathbb E_\theta(Y^\star)^2\,\Pi(d\theta\mid X)<\infty$, then with
  $\mu(\theta)=\mathbb E_\theta Y^\star$ and
  $v(\theta)=\mathop{\mathrm{Var}}_\theta Y^\star$,
  $$\mathop{\mathrm{Var}}(Y^\star\mid X)
  =\mathbb E[v(\theta)\mid X]
  +\mathop{\mathrm{Var}}(\mu(\theta)\mid X).$$
  Under normal sampling with the improper prior of item 4 and a proper
  posterior, $(Y^\star-\bar X)/(s\sqrt{1+1/n})$ has posterior predictive
  law $t_{n-1}$, for $n\ge2$ and $s>0$.

* **9. Bayes factors.** Let models $M_0,M_1$ have positive prior
  probabilities and proper within-model priors, with finite positive
  marginal densities $m_0(x),m_1(x)$. Then
  $$\frac{P(M_1\mid x)}{P(M_0\mid x)}
  =\frac{m_1(x)}{m_0(x)}\frac{P(M_1)}{P(M_0)}.$$
  The ratio $m_1/m_0$ is the Bayes factor. Under $0$–$1$ model-selection
  loss, choosing a model of largest posterior probability is a Bayes
  decision. If the within-model prior of $M_1$ is an improper density
  $\pi_1$, replacing $\pi_1$ by $c\pi_1$, $c>0$, multiplies
  $m_1(x)=\int f_1(x\mid\theta)\pi_1(\theta)\,d\theta$ and hence the ratio
  $m_1/m_0$ by $c$, so the improper prior does not determine a Bayes
  factor.

### Credible regions, point nulls, and hierarchical shrinkage

Suppose the posterior has density $\pi(\theta\mid x)$ with respect to
Lebesgue measure on $\mathbb R^k$. A set $C$ is a **highest posterior
density region** of level $1-\alpha$ when
$\{\theta:\pi(\theta\mid x)>k_\alpha\}\subset C\subset
\{\theta:\pi(\theta\mid x)\ge k_\alpha\}$, where $k_\alpha$ is the largest
$k$ for which $\{\theta:\pi(\theta\mid x)\ge k\}$ has posterior content at
least $1-\alpha$.

* **10. Highest posterior density regions.** Let $C$ be a highest
  posterior density region with posterior content exactly $1-\alpha$ and
  with $k_\alpha>0$. Then $C$ has the smallest Lebesgue volume among all
  measurable sets of posterior content at least $1-\alpha$. For a
  posterior density on the line that is symmetric about a point $c$ and
  nonincreasing in $|\theta-c|$, $C$ may be taken to be the equal-tailed
  credible interval. The construction is not invariant under
  reparameterization: there are posterior densities on the line and
  increasing smooth bijections $g$ of $\mathbb R$ for which $g(C)$ is not a
  highest posterior density region for the image posterior. In the model
  $X\sim N(\theta,\sigma^2)$ with $\sigma$ known and the flat prior, the
  region is $[X-z_{\alpha/2}\sigma,\,X+z_{\alpha/2}\sigma]$, which is also
  the exact confidence interval of level $1-\alpha$.

* **11. Point-null Bayes factor and Lindley's paradox.** Let
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
  $\theta\ne\theta_0$, $B_{01}\to0$ almost surely. For every prior $g_1$
  on $\{\theta\ne\theta_0\}$, the Bayes factor
  $B_{01}(g_1)=f(x\mid\theta_0)/\int f(x\mid\theta)\,g_1(d\theta)$ of $H_0$
  to $H_1$ with prior $g_1$ under $H_1$, where $f(x\mid\theta)$ is the
  density of $x=\bar X$, satisfies
  $$B_{01}(g_1)\ge\frac{f(x\mid\theta_0)}{\sup_{\theta\ne\theta_0}f(x\mid\theta)},$$
  which equals $\exp(-z^2/2)$ in this normal model.

* **12. Hierarchical normal model.** Let $y_j\mid\theta_j\sim
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

* **13. Empirical Bayes form of the James–Stein estimator.** Let
  $X\sim N_p(\theta,I_p)$ and let the $\theta_i$ be independent
  $N(0,\tau^2)$. The posterior mean is $(1-B)X$ with
  $B=1/(1+\tau^2)$, and marginally $X\sim N_p(0,(1+\tau^2)I_p)$. For
  $p\ge3$, $(p-2)/\|X\|^2$ is unbiased for $B$ under this marginal law,
  and substituting it gives the James–Stein estimator of SYNOPSIS101, item 57. Substituting instead the marginal maximum likelihood estimator
  of $\tau^2$, truncated at zero, gives
  $(1-p/\|X\|^2)_+X$. If the common prior mean $\mu$ is also unknown and
  $S=\sum_i(X_i-\bar X)^2$, then for $p\ge4$ the quantity $(p-3)/S$ is
  unbiased for $B$, giving the Efron–Morris estimator
  $\bar X+(1-(p-3)/S)(X_i-\bar X)$, which shrinks toward the grand mean.

* **14. Tweedie's formula and Robbins' estimator.** Let
  $f(x\mid\theta)=h(x)\exp(\theta\cdot x-\psi(\theta))$ be a density on
  $\mathbb R^k$ with respect to Lebesgue measure, let the prior $g$ be
  arbitrary, and let $m$ be the marginal density, assumed positive and
  differentiable under the integral sign. Then
  $$\mathbb E[\theta\mid X=x]=\nabla\log m(x)-\nabla\log h(x).$$
  The Gaussian case is item 69. For Poisson sampling,
  $X\mid\theta\sim\mathop{\mathrm{Poi}}(\theta)$ with any prior on
  $(0,\infty)$, the posterior mean is
  $$\mathbb E[\theta\mid X=x]=(x+1)\frac{m(x+1)}{m(x)},$$
  where $m$ is the marginal probability mass function. For independent
  $X_1,\ldots,X_n$ with law $m$ and $N_n(x)=\#\{i\le n:X_i=x\}$, Robbins'
  nonparametric empirical Bayes estimator is
  $(x+1)N_n(x+1)/N_n(x)$; for every $x$ with $m(x)>0$ it converges almost
  surely to $\mathbb E[\theta\mid X=x]$ as $n\to\infty$.

### Nonparametric Bayes, posterior asymptotics, and inverse problems

Let $\mathcal X$ be a standard Borel space and let $\alpha$ be a finite
nonzero measure on $\mathcal X$. Write $|\alpha|=\alpha(\mathcal X)$ and
$H=\alpha/|\alpha|$.

* **15. Dirichlet process.** A random probability measure $P$ is a Dirichlet
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

* **16. Pólya urn scheme and distinct values.** If $X_1,X_2,\ldots$ are
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

* **17. Doob's consistency theorem.** Consider a dominated model
  $\{P_\theta:\theta\in\Theta\}$ on a standard Borel sample space, with
  $\Theta$ Polish with its Borel $\sigma$-field, and a prior $\Pi$ on
  $\Theta$. Assume $\theta\mapsto P_\theta(A)$ is measurable for every
  measurable $A$, and let $X_1,X_2,\ldots$ be independent with law
  $P_\theta$. If $\theta\mapsto P_\theta$ is injective, then there is a
  $\Pi$-null set $N$ such that for every $\theta\notin N$ and every
  neighborhood $U$ of $\theta$, the posterior probability of $U$ given
  $X_1,\ldots,X_n$ tends to $1$, $P_\theta^\infty$-almost surely.

* **18. Schwartz's theorem.** Let $\Pi$ be a prior on a set of probability
  densities relative to a $\sigma$-finite measure, let $X_1,X_2,\ldots$ be
  independent with law $P_0$ of density $p_0$, and write
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

* **19. Contraction rate of Ghosal, Ghosh, and van der Vaart.** Let
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

* **20. Linear inverse problems.** Let $A$ be a compact injective operator
  between separable Hilbert spaces with singular system
  $Ae_j=\kappa_jg_j$, where $(e_j)$ and $(g_j)$ are orthonormal and
  $c_0^{-1}j^{-a}\le\kappa_j\le c_0j^{-a}$ for constants $c_0\ge1$,
  $a\ge0$. Observe $Y=Af+\varepsilon\mathbb W$ for white noise
  $\mathbb W$; equivalently $Y_j=\kappa_jf_j+\varepsilon Z_j$, $j\ge1$, with
  $f_j=\langle f,e_j\rangle$ and $Z_j$ independent standard normal. For
  $\beta,R>0$ let $S^\beta(R)=\{f:\sum_jj^{2\beta}f_j^2\le R^2\}$ and put
  $r=2\beta/(2\beta+2a+1)$. There are constants $0<c\le C$, depending
  only on $a$, $\beta$, $R$, and $c_0$, such that for $0<\varepsilon\le1$
  $$c\,\varepsilon^r\le\inf_{\hat f}\sup_{f\in S^\beta(R)}
  \bigl(\mathbb E_f\|\hat f-f\|^2\bigr)^{1/2}\le C\varepsilon^r,$$
  the infimum being over all estimators. If the prior makes the $f_j$
  independent $N(0,j^{-1-2\beta})$, then for every $M_\varepsilon\to\infty$
  as $\varepsilon\to0$,
  $$\sup_{f_0\in S^\beta(R)}\mathbb E_{f_0}
  \Pi\bigl(\|f-f_0\|\ge M_\varepsilon\varepsilon^r\bigm|Y\bigr)\to0.$$

<a id="synopsis-104b"></a>

## 104B. Monte Carlo, Langevin Dynamics, and Particle Methods

Discrete-time Monte Carlo and Markov chain samplers come first; the continuous-time sampling dynamics, stochastic approximation, and interacting particle systems that describe or replace them follow.

### Monte Carlo and Markov chain Monte Carlo

* **21. Importance sampling.** Let the target probability have density $p$ and
  let the proposal have density $q$, with $p$ absolutely continuous with
  respect to $q$. If $\mathbb E_q[(p/q)|h|]<\infty$, then
  $\mathbb E_p h=\mathbb E_q[(p/q)h]$. For an independent sample from $q$, the
  average of $(p/q)(X_i)h(X_i)$ is unbiased for $\mathbb E_p h$, with variance
  $n^{-1}\bigl(\mathbb E_q[(p/q)^2h^2]-(\mathbb E_p h)^2\bigr)$ when
  $\mathbb E_q[(p/q)^2h^2]<\infty$. With $w_i=p(X_i)/q(X_i)$, the
  self-normalized estimator $\sum_iw_ih(X_i)/\sum_jw_j$ converges almost
  surely to $\mathbb E_p h$ whenever $\mathbb E_q[(p/q)|h|]<\infty$.

Let $\pi$ be a target density on a measurable space and let $q(x,dy)$ be a
proposal kernel that admits a density $q(x,y)$ in the second variable.

* **22. Metropolis–Hastings.** Define the acceptance probability
  $$\alpha(x,y)=\min\Bigl(1,
  \frac{\pi(y)q(y,x)}{\pi(x)q(x,y)}\Bigr)$$
  when the denominator is positive, and $\alpha(x,y)=1$ when
  $\pi(x)q(x,y)=0$. The kernel that proposes $Y\sim q(x,\cdot)$ and moves
  from $x$ to $Y$ with probability $\alpha(x,Y)$, remaining at $x$ otherwise,
  is reversible with respect to $\pi$ and therefore leaves $\pi$ invariant.

* **23. Gibbs sampling.** Suppose the joint distribution is absolutely
  continuous with respect to a product measure and its density is positive on
  the product of the coordinate supports. The kernel that updates one
  coordinate from its conditional distribution given the others, in a
  deterministic or a random scan, leaves the joint distribution invariant.

* **24. Central limit theorem for Markov chain Monte Carlo.** Let
  $(X_t)_{t\ge0}$ be a Markov chain with invariant probability $\pi$,
  satisfying the drift and minorization condition of CKMA SYNOPSIS08,
  item 69. If $f$ is measurable and $\mathbb E_\pi|f|^{2+\delta}<\infty$ for
  some $\delta>0$, then for every initial distribution
  $$\sqrt n\Bigl(n^{-1}\sum_{t=1}^n f(X_t)-\pi(f)\Bigr)
  \Rightarrow N(0,\sigma^2(f)),$$
  where
  $$\sigma^2(f)=\mathop{\mathrm{Var}}_\pi(f(X_0))
  +2\sum_{k=1}^\infty\mathop{\mathrm{Cov}}_\pi\bigl(f(X_0),f(X_k)\bigr)$$
  and the series converges absolutely.

For a density $q$ on the parameter, the **evidence lower bound** of a sample
$y$ is $\mathbb E_q\log p(y,\theta)-\mathbb E_q\log q(\theta)$.

* **25. Evidence lower bound.** Suppose $0<p(y)<\infty$. For every
  probability density $q$ absolutely continuous with respect to the
  posterior and with $\mathbb E_q|\log p(y,\theta)|$ and
  $\mathbb E_q|\log q(\theta)|$ finite,
  $$\log p(y)=\mathbb E_q\log p(y,\theta)-\mathbb E_q\log q(\theta)
  +\mathop{\mathrm{KL}}(q\,\|\,p(\cdot\mid y)).$$
  Maximizing the evidence lower bound over a family of densities $q$ is
  therefore the same as minimizing the Kullback–Leibler divergence from $q$
  to the posterior. A mean-field family restricts $q$ to a product of
  coordinate laws. The construction of such families is in Section 107.

* **26. Self-normalized importance-sampling limit.** In item 21, put
  $w=p/q$, $\mu=\mathbb E_p h$, and suppose
  $\mathbb E_q[w^2(h-\mu)^2]<\infty$ and $\mathbb E_q[w|h|]<\infty$.
  For independent proposal draws,
  $$\sqrt n\left(\frac{\sum_iw(X_i)h(X_i)}{\sum_iw(X_i)}-\mu\right)
  \Rightarrow N\left(0,\mathbb E_q[w^2(h-\mu)^2]\right).$$
  Multiplying all weights by a common unknown constant leaves the estimator
  unchanged.

* **27. Conditional Monte Carlo.** If $(U_i,V_i)$ are independent copies
  and $H(U,V)\in L^2$, replacing $H(U_i,V_i)$ by
  $\mathbb E[H(U_i,V_i)\mid U_i]$ in a Monte Carlo average preserves its
  expectation and does not increase its variance, by the law of total
  variance.

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

* **31. Convergence of Metropolis–Hastings.** Suppose the chain of item 22 is $\pi$-irreducible. Then it is Harris recurrent, and for every
  $h\in L^1(\pi)$ the averages $n^{-1}\sum_{t\le n}h(X_t)$ converge to
  $\pi(h)$ almost surely from every starting point. If it is also
  aperiodic, then $P^n(x,\cdot)\to\pi$ in total variation for every $x$,
  as in CKMA SYNOPSIS08, item 68. Irreducibility holds if $q(x,y)>0$ for
  all $x,y$ in the support of $\pi$, and aperiodicity holds if
  $P(\alpha(X,Y)<1)>0$ for $X\sim\pi$ and $Y\sim q(X,\cdot)$. On $\mathbb R^d$, if the support of $\pi$ is
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
  density, the chain is geometrically ergodic only if
  $\int e^{s|x|}\pi(dx)<\infty$ for some $s>0$. If $\pi$ is symmetric
  and log-concave in the tails, in the sense that
  $\log\pi(x)-\log\pi(y)\ge a|y-x|$ for some $a>0$ and $x_1$ whenever
  $x_1\le x<y$ or $y<x\le-x_1$, the chain is geometrically ergodic.

* **33. Gibbs sampling as Metropolis–Hastings; two-stage samplers.**
  Each coordinate update of item 23 is a Metropolis–Hastings step whose
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
  larger than $T^{-1}\sum_{t\le T}h(X^{(t)})$ for every $T$, under
  stationarity. When $X$ is a parameter and $Y$ is missing data, the
  scheme is called data augmentation.

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
  momentum refreshment. The exact Hamiltonian flow conserves $H$, so if
  it replaced $\Phi$ the acceptance probability would be identically $1$.

### Mean-field coordinate ascent

* **36. Coordinate-ascent variational updates.** In item 25, restrict
  $q=\prod_jq_j$ to a product over blocks $\theta=(\theta_1,\ldots,\theta_J)$.
  With the factors $q_\ell$, $\ell\ne j$, held fixed, the evidence lower
  bound is maximized over $q_j$ by
  $$q_j^*(\theta_j)\propto\exp\Bigl(\mathbb E_{q_{-j}}\log p(y,\theta)\Bigr),$$
  provided the right side is integrable, where $\mathbb E_{q_{-j}}$
  averages over the other blocks. Indeed, as a function of $q_j$, the
  evidence lower bound differs from
  $-\mathop{\mathrm{KL}}(q_j\,\|\,q_j^*)$ by a constant. Cycling through
  these updates therefore never decreases the evidence lower bound.

### Langevin dynamics, sampling, and gradient flows

Let $V:\mathbb R^d\to\mathbb R$ be twice continuously differentiable with
$\nabla V$ globally Lipschitz and $\int e^{-V(x)}dx<\infty$, and let
$\pi(dx)\propto e^{-V(x)}\,dx$. The **overdamped Langevin diffusion**,
which then has a unique nonexplosive strong solution, is
$$dX_t=-\nabla V(X_t)\,dt+\sqrt2\,dW_t.$$

* **37. Invariant measure and gradient-flow structure.** The probability
  $\pi$ is invariant for the diffusion. Its marginal flow is the
  $W_2$ gradient flow of $\rho\mapsto\int\rho\log\rho+\int V\,d\rho$, and
  therefore solves $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$.
  That identification is CKMA SYNOPSIS39, item 62.

* **38. Contraction under strong convexity.** If $\nabla^2V\ge mI$ for some
  $m>0$, then
  $$W_2(\mu_t,\pi)\le e^{-mt}W_2(\mu_0,\pi)$$
  for the law $\mu_t$ of $X_t$. The same convexity makes the relative
  entropy $m$-displacement-convex, so the $\mathrm{EVI}_m$ contraction of
  CKMA SYNOPSIS39, item 59, applies.

The **unadjusted Langevin algorithm** is the Euler–Maruyama discretization
$$X_{(n+1)h}=X_{nh}-h\nabla V(X_{nh})+\sqrt{2h}\,\xi_{n+1},$$
with $\xi_n$ standard normal. Write $\kappa=\beta/\alpha$ when
$\alpha I\preceq\nabla^2V\preceq\beta I$ and $\alpha>0$.

* **39. Iteration complexity of Langevin Monte Carlo.** Suppose
  $\alpha I\preceq\nabla^2V\preceq\beta I$, $\alpha>0$, and
  $\varepsilon\in(0,\sqrt d]$, and write $\hat\mu_{nh}$ for the law of the
  $n$-th iterate. There are universal constants $c,C>0$ such that, with
  step size $h=c\varepsilon^2/(\beta d)$ and
  $$N\ge C\,\frac{\kappa d}{\varepsilon^2}
  \log\left(e+\frac{\alpha W_2^2(\hat\mu_0,\pi)}{\varepsilon^2}\right),$$
  one has $\sqrt\alpha\,W_2(\hat\mu_{Nh},\pi)\le\varepsilon$, and the
  mixture of marginal laws $\bar\mu=N^{-1}\sum_{j=N+1}^{2N}\hat\mu_{jh}$
  satisfies $\sqrt{\mathop{\mathrm{KL}}(\bar\mu\|\pi)}\le\varepsilon$.
  This is Chewi's Theorem 4.3.6. The mixture is the law of a uniformly
  randomly selected iterate, not the law of the arithmetic average of the
  iterates.

Let $h:\mathbb R^p\to\mathbb R^p$ satisfy $h(\theta^\star)=0$, and let the
recursion be
$\theta_{n+1}=\theta_n-a_n\bigl(h(\theta_n)+M_{n+1}\bigr)$, where $M_{n+1}$
is a martingale difference sequence with respect to
$\mathcal F_n=\sigma(\theta_0,M_1,\ldots,M_n)$.

* **40. Robbins–Monro convergence and averaging.** Suppose $h$ is
  globally Lipschitz and
  $(\theta-\theta^\star)\cdot h(\theta)\ge
  m\|\theta-\theta^\star\|^2$ for $m>0$. For positive steps with
  $\sum a_n=\infty$, $\sum a_n^2<\infty$, square-integrable initial
  state, and $\mathbb E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K$ for a constant
  $K$, $\theta_n\to\theta^\star$ almost surely.
  For $a_n=n^{-\alpha}$, $1/2<\alpha<1$, suppose additionally that
  $h$ has a locally Lipschitz derivative, with $A=Dh(\theta^\star)$,
  that $\mathbb E[M_{n+1}M_{n+1}^\top\mid\mathcal F_n]\to S$ in
  probability, and that
  $\sup_n\mathbb E[\|M_{n+1}\|^{2+\delta}\mid\mathcal F_n]<\infty$ almost
  surely for some $\delta>0$. Then the averaged iterate
  $\bar\theta_n=n^{-1}\sum_{k=1}^n\theta_k$ satisfies
  $$\sqrt n(\bar\theta_n-\theta^\star)
  \Rightarrow N(0,A^{-1}SA^{-\top}).$$

### Entropy and discretization bias

* **41. Entropy dissipation of Langevin flow.** Write
  $I(\rho\|\pi)=\int\|\nabla\log(\rho/\pi)\|^2\rho\,dx$ for the relative
  Fisher information. Let $\rho_t$ be the law of $X_t$, where $X_0$ has a
  continuously differentiable density $\rho_0$ with $\rho_0/\pi$ bounded
  above and below by positive constants. Then for $t>0$
  $$\frac d{dt}\mathop{\mathrm{KL}}(\rho_t\|\pi)=-I(\rho_t\|\pi).$$
  If $\pi$ satisfies the logarithmic Sobolev inequality
  $\mathop{\mathrm{KL}}(\rho\|\pi)\le I(\rho\|\pi)/(2m)$,
  then $\mathop{\mathrm{KL}}(\rho_t\|\pi)\le
  e^{-2mt}\mathop{\mathrm{KL}}(\rho_0\|\pi)$. Strong convexity
  $\nabla^2V\ge mI$ is a sufficient condition.

* **42. Exact Gaussian discretization bias.** For $V(x)=x^\top Ax/2$,
  $A>0$, the diffusion has invariant law $N(0,A^{-1})$.
  The unadjusted chain is stable for $0<h<2/\lambda_{\max}(A)$
  and has invariant covariance
  $$\Sigma_h=(A-\tfrac h2A^2)^{-1}.$$
  This follows from the discrete covariance equation
  $\Sigma_h=(I-hA)\Sigma_h(I-hA)+2hI$. From every initial law the chain
  converges in distribution to $N(0,\Sigma_h)$, and
  $\Sigma_h\ne A^{-1}$ for every such $h$.

### Variational time stepping and functional inequalities

Write $\mathcal F(\rho)=\int\rho\log\rho\,dx+\int V\rho\,dx$, which differs
from $\mathop{\mathrm{KL}}(\rho\|\pi)$ by a constant. For a time step
$\tau>0$ and a probability density $\rho_0$, the **JKO scheme** sets
$\rho_0^\tau=\rho_0$ and lets $\rho_{k+1}^\tau$ minimize
$$\rho\mapsto\frac1{2\tau}W_2^2(\rho,\rho_k^\tau)+\mathcal F(\rho)$$
over probability densities with finite second moment. Its piecewise-constant
interpolation is $\rho^\tau(t)=\rho_k^\tau$ for $k\tau\le t<(k+1)\tau$.

* **43. Jordan–Kinderlehrer–Otto theorem.** Let $V$ be smooth and
  nonnegative with $\|\nabla V\|\le C(V+1)$, and let $\rho_0$ have
  finite second moment and $\mathcal F(\rho_0)<\infty$. Then every step
  of the JKO scheme has a unique minimizer. As $\tau\downarrow0$,
  $\rho^\tau(t)$ converges weakly in $L^1$ for every $t\ge0$, and
  strongly in $L^1((0,T)\times\mathbb R^d)$ for every $T$, to the unique
  solution of $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$ with
  initial datum $\rho_0$. In this item the standing hypotheses on $V$ are
  replaced by those stated, and $e^{-V}$ need not be integrable;
  the general metric version is CKMA SYNOPSIS39, items 57 and 61–62.

The **chi-squared divergence** is
$\chi^2(\mu\|\pi)=\mathop{\mathrm{Var}}_\pi(d\mu/d\pi)$ if $\mu\ll\pi$, and
$+\infty$ otherwise. The target $\pi$ satisfies a **Poincaré inequality**
with constant $C_P$ if $\mathop{\mathrm{Var}}_\pi f\le C_P\,\mathbb E_\pi\|\nabla f\|^2$
for all smooth $f$, and a **logarithmic Sobolev inequality** with constant
$C_{LS}$ if $\mathop{\mathrm{KL}}(\mu\|\pi)\le\tfrac{C_{LS}}2
\mathbb E_\mu\|\nabla\log(d\mu/d\pi)\|^2$ for all smooth positive $\mu$.
Item 41 is the case $C_{LS}=1/m$.

* **44. Convergence of the Langevin diffusion under functional
  inequalities.** Let $\mu_t$ be the law of $X_t$. The Poincaré
  inequality with constant $C_P$ holds if and only if
  $$\chi^2(\mu_t\|\pi)\le e^{-2t/C_P}\chi^2(\mu_0\|\pi)$$
  for every initial law. The logarithmic Sobolev inequality with constant
  $C_{LS}$ holds if and only if
  $\mathop{\mathrm{KL}}(\mu_t\|\pi)\le e^{-2t/C_{LS}}
  \mathop{\mathrm{KL}}(\mu_0\|\pi)$ for every initial law, and it then
  also gives
  $W_2^2(\mu_t,\pi)\le2C_{LS}e^{-2t/C_{LS}}\mathop{\mathrm{KL}}(\mu_0\|\pi)$
  by the Otto–Villani inequality, CKMA SYNOPSIS14, item 57. The logarithmic
  Sobolev inequality implies the Poincaré inequality with $C_P\le C_{LS}$.
  Neither requires convexity: if $V=V_0+\psi$ with $\nabla^2V_0\ge mI$,
  $m>0$, and $\psi$ bounded, then both hold with constant at most
  $e^{\sup\psi-\inf\psi}/m$, by CKMA SYNOPSIS14, items 38 and 48.
  For $\pi=N(0,I_d)$ and $\mu_0=N(0,s^2I_d)$ with $0<s^2<2$,
  $s^2\ne1$, one has
  $\chi^2(\mu_0\|\pi)=(s^2(2-s^2))^{-d/2}-1$, exponential in $d$, while
  $\mathop{\mathrm{KL}}(\mu_0\|\pi)=\tfrac d2(s^2-1-\log s^2)$, linear in
  $d$.

### Unadjusted, stochastic-gradient, and Metropolis-adjusted Langevin

Let $\hat\mu_{nh}$ denote the law of the $n$-th iterate of the unadjusted
Langevin algorithm above. The potential is **$\beta$-smooth** if $\nabla V$
is $\beta$-Lipschitz.

* **45. Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  Suppose $\pi$ satisfies the logarithmic Sobolev inequality with
  constant $1/\alpha$ and $V$ is $\beta$-smooth; $V$ need not be convex.
  There is a universal constant $C$ such that for $0<h\le\alpha/(4\beta^2)$ and
  all $N$,
  $$\mathop{\mathrm{KL}}(\hat\mu_{Nh}\|\pi)\le
  e^{-\alpha Nh}\mathop{\mathrm{KL}}(\hat\mu_0\|\pi)
  +C\,\frac{\beta^2dh}\alpha$$
  (Vempala–Wibisono). With $\kappa=\beta/\alpha$, it follows that there are
  universal constants $c,C'$ such that for
  $0<\varepsilon\le\sqrt d$ the step
  $h=c\varepsilon^2/(\beta\kappa d)$ gives
  $\mathop{\mathrm{KL}}(\hat\mu_{Nh}\|\pi)\le\varepsilon^2$ whenever
  $N\ge C'\kappa^2d\varepsilon^{-2}
  \log(e+\mathop{\mathrm{KL}}(\hat\mu_0\|\pi)/\varepsilon^2)$.
  If instead $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$, there are
  universal constants $c,C$ such that for $0<h\le c/(\beta\kappa)$ and
  all $N$, a synchronous coupling gives
  $$W_2(\hat\mu_{Nh},\pi)\le e^{-\alpha Nh/2}W_2(\hat\mu_0,\pi)
  +C\,\frac{\beta\sqrt{dh}}\alpha.$$
  In both bounds the second term does not tend to zero as $N\to\infty$
  at fixed $h$; compare item 42.

A **stochastic gradient oracle** returns, at each query point $x$ and with
fresh randomness, a vector $\widehat{\nabla V}(x)$ with
$\mathbb E\widehat{\nabla V}(x)=\nabla V(x)$ and
$\mathbb E\|\widehat{\nabla V}(x)-\nabla V(x)\|^2\le\sigma^2$; a minibatch
gradient of a sum over data points is the typical case. **Stochastic
gradient Langevin dynamics** replaces $\nabla V$ by
$\widehat{\nabla V}$ in the unadjusted Langevin algorithm.

* **46. Stochastic gradient Langevin dynamics.** Started at the same point
  $x$ and driven by the same Gaussian increment, one step of the
  stochastic-gradient update $\hat X_h$ and one step of the
  exact-gradient update $X_h$ satisfy $\mathbb E\hat X_h=\mathbb EX_h$ and
  $\mathbb E\|\hat X_h-X_h\|^2\le\sigma^2h^2$. Now let $\hat X_{nh}$ be
  the stochastic-gradient chain with law $\hat\mu_{nh}$, write
  $\zeta_n=\widehat{\nabla V}(\hat X_{nh})-\nabla V(\hat X_{nh})$ for its
  gradient errors, and suppose that
  $\mathbb E[\zeta_n\mid\hat X_{nh}]=0$,
  $\mathbb E\|\zeta_n\|^2\le\sigma^2$, the Gaussian increments are
  independent of each other and of $\hat X_0$, and $\xi_{n+1}$ is
  independent of $(\zeta_0,\ldots,\zeta_n)$. If
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and
  $0<h\le2/(\alpha+\beta)$, then for every $N$
  $$W_2(\hat\mu_{Nh},\pi)\le(1-\alpha h)^NW_2(\hat\mu_0,\pi)
  +1.65\,\frac\beta\alpha(hd)^{1/2}
  +\frac{\sigma^2h^{1/2}}{1.65\,\beta d^{1/2}+\sigma\alpha^{1/2}}.$$
  The first two terms are the bound for the exact-gradient chain; the
  last is the price of the gradient noise and vanishes when $\sigma=0$.

The **Metropolis-adjusted Langevin algorithm** (MALA) uses the
unadjusted step $y=x-h\nabla V(x)+\sqrt{2h}\,\xi$ as the proposal of the
Metropolis–Hastings algorithm of item 22, with proposal density
$q(x,y)\propto\exp(-\|y-x+h\nabla V(x)\|^2/(4h))$. Its kernel leaves $\pi$
invariant for every $h>0$, so it has no discretization bias. The random-walk
Metropolis algorithm uses $y=x+\sqrt{2h}\,\xi$ instead. The
**$\tfrac12$-lazy** version of a Markov kernel $K$ is
$\tfrac12(\delta_x+K(x,\cdot))$. For a constant $M\ge1$, a start $\mu_0$
is **$M$-warm** if $\mu_0(A)\le M\pi(A)$ for every Borel set $A$; then
$\chi^2(\mu_0\|\pi)\le M-1$. The **$\varepsilon$-mixing time** from
$\mu_0$ is the least $n$ with $\|\mu_n-\pi\|_{\mathrm{TV}}\le\varepsilon$,
where $\mu_n$ is the law of the $n$-th iterate.

* **47. Mixing of Metropolis-adjusted Langevin.** Suppose
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$, $\kappa=\beta/\alpha$,
  and $0<\varepsilon<1$. There are universal constants $c_0,c_1,c_2>0$
  such that, with
  $\Lambda=\log\max\{\kappa,d,M/\varepsilon,c_2\}$, the $\tfrac12$-lazy
  MALA with step $h=c_0/(\beta d^{1/2}\Lambda^2)$ has
  $\varepsilon$-mixing time at most $c_1\kappa d^{1/2}\Lambda^3$ from
  every $M$-warm start. Conversely, there are universal constants
  $c_3,c_4>0$ with the following property: for all $a,b>0$ there is
  $N_{a,b}$ such that whenever $d>N_{a,b}$, $3\le\kappa\le ad^b$,
  $M\ge12$, and $h>0$, some target with
  $\alpha I\preceq\nabla^2V\preceq\beta I$ and some $M$-warm start give
  the $\tfrac12$-lazy MALA with step $h$ an $\varepsilon$-mixing time
  at least
  $$\frac{c_3\kappa d^{1/2}}{(\max\{\log\kappa,\log d\})^3}
  \log\frac{c_4}\varepsilon.$$
  So the warm-start dimension dependence $d^{1/2}$ is sharp up to
  logarithmic factors. From the cold start $N(x^\star,\beta^{-1}I)$, with
  $x^\star$ the minimizer of $V$, a suitably tuned MALA, and likewise
  random-walk Metropolis, reaches
  $\sqrt{\chi^2(\mu_N\|\pi)}\le\varepsilon$ after
  $N\le C\kappa d\,(\log(e+\kappa d))^r(\log(e+1/\varepsilon))^r$
  iterations, for universal constants $C,r>0$.

### Kinetic Langevin dynamics

The **underdamped**, or kinetic, **Langevin diffusion** with friction
$\gamma>0$ is
$$dX_t=P_t\,dt,\qquad dP_t=-\nabla V(X_t)\,dt-\gamma P_t\,dt+\sqrt{2\gamma}\,dW_t$$
on $\mathbb R^{2d}$. Hamiltonian Monte Carlo, which refreshes the momentum
at discrete times, is item 35; the kinetic diffusion
refreshes it continuously.

* **48. Invariance, contraction, and hypocoercivity.** The probability
  $\boldsymbol\pi(dx\,dp)\propto e^{-V(x)-\|p\|^2/2}\,dx\,dp=\pi\otimes N(0,I)$
  is invariant, and its $x$-marginal is $\pi$. The process is not
  reversible: the law solves
  $$\partial_t\boldsymbol\pi_t=\nabla\cdot\left(\boldsymbol\pi_t\,J_\gamma
  \nabla\log\frac{\boldsymbol\pi_t}{\boldsymbol\pi}\right),\qquad
  J_\gamma(a,b)=(-b,\;a+\gamma b),$$
  where $J_\gamma$ acts on the pair of $x$- and $p$-gradients. If
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and
  $\gamma\ge\sqrt{2\beta}$, two copies driven by the same Brownian motion
  satisfy $|||\Delta_t|||\le e^{-\alpha t/\gamma}|||\Delta_0|||$, where
  $\Delta_t$ is the difference of the two states at time $t$ and
  $|||(x,p)|||^2=\|x\|^2+\|x+2p/\gamma\|^2$. If $\pi$ satisfies a Poincaré inequality
  with constant $1/\alpha$, $V$ is $\beta$-smooth, and
  $\gamma=c_0\sqrt\beta$, then the relative density $f_t=d\boldsymbol\pi_t/d\boldsymbol\pi-1$
  satisfies
  $$\|f_t\|^2+\tfrac1\beta\|\nabla_xf_t\|^2+\|\nabla_pf_t\|^2
  \le Ce^{-c\alpha t/\sqrt\beta}\bigl(\|f_0\|^2+\tfrac1\beta\|\nabla_xf_0\|^2
  +\|\nabla_pf_0\|^2\bigr)$$
  in $L^2(\boldsymbol\pi)$, with $c,C>0$ depending only on $c_0$. If
  instead $\pi$ satisfies a logarithmic Sobolev inequality with constant
  $1/\alpha$, with the same $\gamma$, there are real constants $a,b,c_1$
  and a universal constant $c'>0$ such that
  $$\mathcal L_t=\mathop{\mathrm{KL}}(\boldsymbol\pi_t\|\boldsymbol\pi)
  +\mathbb E_{\boldsymbol\pi_t}\Bigl\langle\nabla\log\frac{\boldsymbol\pi_t}
  {\boldsymbol\pi},\Bigl(\begin{pmatrix}a/\beta&b/\sqrt\beta\\
  b/\sqrt\beta&c_1\end{pmatrix}\otimes I_d\Bigr)\nabla\log\frac{\boldsymbol\pi_t}
  {\boldsymbol\pi}\Bigr\rangle$$
  satisfies $\mathcal L_t\le e^{-c'\alpha t/\sqrt\beta}\mathcal L_0$. This is the
  hypocoercive mechanism of CKMA SYNOPSIS34, item 75, in a confining
  potential.

### The ordinary differential equation method

For the recursion of item 40, the **limiting equation** is
$\dot\theta=-h(\theta)$, with flow $\Phi_t$. A compact set $A$ is
**invariant** if $\Phi_t(A)=A$ for all real $t$. It is **internally chain
transitive** if, in addition, for all $x,y\in A$ and all
$\varepsilon,T>0$ there are points $x_0,\ldots,x_n=y$ in $A$ with
$\|x_0-x\|<\varepsilon$ such that the trajectory from each $x_i$ enters
the $\varepsilon$-neighbourhood of $x_{i+1}$ after a time at least $T$.

* **49. Benaïm's limit-set theorem.** Suppose $h$ is globally Lipschitz,
  $a_n>0$, $\sum a_n=\infty$, $\sum a_n^2<\infty$, $(M_n)$ is a
  martingale difference sequence with respect to
  $\mathcal F_n=\sigma(\theta_0,M_1,\ldots,M_n)$ satisfying
  $\mathbb E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K(1+\|\theta_n\|^2)$, and
  $\sup_n\|\theta_n\|<\infty$ almost surely. Then almost surely $\theta_n$
  converges to a, possibly sample-path-dependent, compact connected
  internally chain transitive invariant set of the limiting equation.
  Consequently, if $U\ge0$ is continuously differentiable,
  $U(\theta)\to\infty$ as $\|\theta\|\to\infty$, the set
  $H=\{U=0\}$ is nonempty, and $\langle h,\nabla U\rangle\ge0$ with
  equality exactly on $H$, then the distance from $\theta_n$ to $H$ tends
  to zero almost surely.
  If the only internally chain transitive invariant sets are isolated
  equilibria, $\theta_n$ converges almost surely to a, possibly random,
  equilibrium. Moreover, let $t_n=\sum_{k<n}a_k$ and let $\bar\theta$ be
  the piecewise linear function with $\bar\theta(t_n)=\theta_n$. Then for
  every $T>0$, almost surely,
  $$\lim_{s\to\infty}\sup_{0\le u\le T}
  \|\bar\theta(s+u)-\Phi_u(\bar\theta(s))\|=0;$$
  this is the ordinary differential equation method of Kushner–Clark and
  Ljung.

* **50. Stability by the scaling limit.** Suppose the hypotheses of item 49 other than boundedness hold. Suppose further that
  $h_c(\theta)=h(c\theta)/c$ converges, as $c\to\infty$, uniformly on
  compact sets to a limit $h_\infty$, and that the origin is the unique
  globally asymptotically stable equilibrium of
  $\dot\theta=-h_\infty(\theta)$. Then $\sup_n\|\theta_n\|<\infty$ almost
  surely, so the conclusion of item 49 holds (Borkar–Meyn). For example,
  if $h(\theta)=A\theta+b+o(\|\theta\|)$ with $-A$ Hurwitz, then
  $h_\infty(\theta)=A\theta$.

### Particle methods, data assimilation, and training dynamics

Let $b(x,\mu)$ be a Lipschitz drift on $\mathbb R^d\times\mathcal P_1$.
The **McKean–Vlasov equation** is the law of
$d\bar X_t=b(\bar X_t,\mathop{\mathrm{Law}}(\bar X_t))\,dt+dW_t$. The
$N$-particle system uses the same drift evaluated at the empirical measure
of the $N$ particles.

* **51. Propagation of chaos.** Assume a drift globally Lipschitz in
  position and in $W_1$ of the measure, independent Brownian drivers,
  and independent identically distributed initial states with finite
  second moment, independent of those drivers. Then the limiting equation
  and the particle systems have unique strong solutions, and for every
  $T<\infty$ and every fixed $k$, the joint law of the paths on $[0,T]$ of
  the first $k$ particles converges weakly on
  $C([0,T];\mathbb R^{dk})$ to the $k$-fold product of the McKean–Vlasov
  path law as $N\to\infty$.

In a linear-Gaussian state-space model, the **ensemble Kalman** update
replaces the forecast covariance in the Kalman gain by the covariance of a
finite ensemble.

* **52. Ensemble Kalman limit.** Consider the linear-Gaussian model
  $v_{j+1}=Mv_j+\xi_j$, $y_{j+1}=Hv_{j+1}+\eta_{j+1}$, with
  $v_0\sim N(m_0,C_0)$, $\xi_j\sim N(0,\Sigma)$, $\eta_j\sim N(0,R)$,
  $R>0$, all independent, and fixed observations $y_1,y_2,\ldots$. Start
  from $N$ independent draws from $N(m_0,C_0)$; at each step form the
  forecasts $X_i^f=MX_i^a+\xi_i$ with independent $\xi_i\sim N(0,\Sigma)$,
  let $C_N$ be their empirical covariance, and apply the
  perturbed-observation update
  $$X_i^a=X_i^f+K_N(y+\eta_i-HX_i^f),\qquad
  \eta_i\sim N(0,R),$$
  with $K_N=C_NH^\top(HC_NH^\top+R)^{-1}$ and independent $\eta_i$. At each
  fixed assimilation time, the empirical mean and covariance of the
  forecast and of the analysis ensemble converge almost surely, as
  $N\to\infty$, to the Kalman predictor and Kalman filter mean and
  covariance. If instead $\eta_i=0$ for all $i$,
  the empirical analysis covariance equals
  $(I-K_NH)C_N-K_NRK_N^\top$, which is smaller than the Kalman analysis
  form $(I-K_NH)C_N$ by the positive semidefinite matrix
  $K_NRK_N^\top$.

Consider a two-layer network whose parameters are $N$ particles and whose
prediction at a feature $x$ is an average of ridge functions of those
particles. Under a $1/N$ scaling of the output weights, gradient descent on
the empirical risk induces a flow on the empirical measure of the particles.

* **53. Mean-field training.** Write
  $f_\rho(x)=\int\phi(x,\theta)\,\rho(d\theta)$ for $\theta\in\mathbb R^p$
  and take the square loss
  $\mathcal R(\rho)=\tfrac12\mathbb E(Y-f_\rho(X))^2$ for a fixed data law
  with $\mathbb EY^2<\infty$. Then
  $\mathcal R(\rho)=\tfrac12\mathbb EY^2-\int V\,d\rho
  +\tfrac12\iint U\,d\rho\,d\rho$ with $V(\theta)=\mathbb E[Y\phi(X,\theta)]$
  and $U(\theta,\theta')=\mathbb E[\phi(X,\theta)\phi(X,\theta')]$, and
  $\Psi(\theta;\rho)=-V(\theta)+\int U(\theta,\theta')\,\rho(d\theta')$ is
  its first variation. Assume $\nabla V$ and $\nabla_\theta U$ are bounded
  and globally Lipschitz. For $N$ particles with empirical measure
  $\rho_N$, the time-scaled gradient flow
  $\dot\theta_i=-N\nabla_{\theta_i}\mathcal R(\rho_N)$ equals
  $\dot\theta_i=-\nabla_\theta\Psi(\theta_i;\rho_N)$. If the initial
  particles are independent with law $\rho_0$ of finite first moment, then
  for every $T<\infty$,
  $\sup_{t\le T}W_1(\rho_N(t),\rho_t)\to0$ almost surely, where $\rho_t$ is
  the unique weak solution with initial datum $\rho_0$ of
  $$\partial_t\rho=\nabla\cdot
  \bigl(\rho\nabla_\theta\Psi(\cdot;\rho)\bigr).$$

**Stein variational gradient descent** with step $\epsilon>0$ moves
particles $x_1,\ldots,x_N$ to $x_i+\epsilon v_{\hat\rho}(x_i)$, where
$v_{\hat\rho}$ is the first integral below with $\rho(y)\,dy$ replaced by
the empirical measure $\hat\rho$ of the particles. The derivation below
applies to densities; the Kullback–Leibler divergence of a finite atomic
measure from a positive continuous target is infinite.

* **54. Stein variational flow.** Let $k$ be a symmetric positive definite
  kernel on $\mathbb R^d$ with reproducing kernel Hilbert space
  $\mathcal H$, continuously differentiable, with $k$ and $\nabla_yk$
  bounded. Let $\pi$ and $\rho$ be positive continuously differentiable
  densities with $\rho$, $\|\nabla\rho\|$, and $\|\nabla\log\pi\|\rho$
  integrable. Define the descent velocity
  $$v_\rho(x)=\int[k(y,x)\nabla\log\pi(y)+\nabla_y k(y,x)]\rho(y)\,dy.$$
  Then
  $v_\rho(x)=\int k(y,x)(\nabla\log\pi(y)-\nabla\log\rho(y))\rho(y)\,dy$,
  $v_\rho\in\mathcal H^d$, and for every $\varphi\in\mathcal H^d$
  $$\langle\varphi,v_\rho\rangle_{\mathcal H^d}
  =\int\langle\nabla\log(\pi/\rho),\varphi\rangle\rho\,dx;$$
  in particular $v_\rho/\|v_\rho\|_{\mathcal H^d}$, when $v_\rho\ne0$,
  maximizes the right side over the unit ball of $\mathcal H^d$. On the
  torus $\mathbb T^d$, with $k$ and $\pi$ smooth and $\rho_t$ a positive
  solution of $\partial_t\rho_t=-\nabla\cdot(\rho_tv_{\rho_t})$ smooth in
  $(t,x)$, the same formulas hold with integrals over $\mathbb T^d$, and
  $$\frac d{dt}\mathop{\mathrm{KL}}(\rho_t\|\pi)
  =-\|v_{\rho_t}\|_{\mathcal H^d}^2.$$

A **particle filter** approximates the filter of a hidden Markov model by a
weighted system of particles, resampled according to the incremental
likelihood weights. The underlying unnormalized measures are the
Feynman–Kac measures of CKMA SYNOPSIS08, item 36.

* **55. Consistency of the particle filter.** If the observation potentials
  are bounded and bounded away from zero, then for the bootstrap particle
  filter with multinomial resampling, at each fixed time $t$ and for every
  bounded measurable $f$, the particle estimate of $\eta_t(f)$ converges
  in probability to $\eta_t(f)$ as the number $N$ of particles tends to
  infinity, where $\eta_t$ is the filter of item 57.

### Quantitative chaos and nonlinear filtering

* **56. A quantitative interaction model.** Suppose
  $b(x,\mu)=b_0(x)+\int K(x,y)\,\mu(dy)$, where $b_0$ is globally
  Lipschitz and $K$ is bounded and globally Lipschitz. Couple the
  particles with independent nonlinear copies using the same initial
  values and Brownian motions. For every finite $T$,
  $$\mathbb E\sup_{t\le T}\|X_t^{i,N}-\bar X_t^i\|^2\le C_T/N,$$
  for independent identically distributed initial values with finite
  second moment, where $C_T$ depends only on $T$, the Lipschitz constants
  of $b_0$ and $K$, and $\sup|K|$.

* **57. Prediction and Bayesian correction.** For a hidden Markov model,
  let $\eta_0$ be the law of the initial state, $M_t$ the state
  transition kernel, and $G_t(x)=p(y_t\mid x)>0$ the likelihood of the
  observed datum $y_t$, $t\ge1$. The filters
  $\eta_t=\mathop{\mathrm{Law}}(X_t\mid y_1,\ldots,y_t)$ and predictors
  $\eta_t^-=\mathop{\mathrm{Law}}(X_t\mid y_1,\ldots,y_{t-1})$ obey
  $$\eta_t^- =\eta_{t-1}M_t,\qquad
  \eta_t(f)=\frac{\eta_t^-(G_tf)}{\eta_t^-(G_t)}.$$
  The data likelihood $Z_t=p(y_1,\ldots,y_t)$ satisfies
  $Z_t=Z_{t-1}\eta_t^-(G_t)$, $Z_0=1$.

* **58. Unbiased particle likelihood.** In a bootstrap particle filter
  with conditionally unbiased resampling, let $X_t^{i,-}$ be the
  predicted particles and set
  $$\hat Z_t=\prod_{s=1}^t
  \left(\frac1N\sum_{i=1}^NG_s(X_s^{i,-})\right).$$
  Then $\mathbb E\hat Z_t=Z_t$, the observations being fixed and the
  expectation taken over the particle system. With multinomial
  resampling and potentials bounded and bounded away from zero, for each
  fixed $t$ there is $C_t$, independent of $N$ and $f$, such that the mean
  squared error of the particle estimate of $\eta_t(f)$ is at most
  $C_t\|f\|_\infty^2/N$ for every bounded measurable $f$.

### Fluctuations, stability, and resampling of particle filters

In the indexing of Del Moral, let $(X_n)_{n\ge0}$ be a Markov chain with
initial law $\eta_0$ and kernels $M_n$, and let $G_n>0$ be bounded
potentials. Put
$$\gamma_n(f)=\mathbb E\Bigl[f(X_n)\prod_{p=0}^{n-1}G_p(X_p)\Bigr],\qquad
\eta_n=\gamma_n/\gamma_n(1),$$
$$Q_{p,n}f(x)=\mathbb E\Bigl[f(X_n)\prod_{q=p}^{n-1}G_q(X_q)\Bigm|X_p=x\Bigr].$$
With $G_p(x)=p(y_p\mid x)$, $\eta_n$ is the one-step predictor $\eta_n^-$
of item 57 and $\gamma_n(1)$ is the likelihood of $y_0,\ldots,y_{n-1}$. The
**bootstrap particle model** draws $\xi_0^1,\ldots,\xi_0^N$ independently
from $\eta_0$ and, given generation $n-1$, draws generation $n$
independently from $\sum_iG_{n-1}(\xi_{n-1}^i)M_n(\xi_{n-1}^i,\cdot)\big/
\sum_iG_{n-1}(\xi_{n-1}^i)$; that is, multinomial selection followed by
mutation. Write $\eta_n^N$ for the empirical measure of generation $n$ and
$\gamma_n^N(1)=\prod_{p<n}\eta_p^N(G_p)$, the estimator of item 58.

* **59. Central limit theorem for Feynman–Kac particle models.**
  Suppose $\inf_xG_p(x)>0$ for every $p$. For bounded measurable $f$ and
  fixed $n$, as $N\to\infty$,
  $$\sqrt N\bigl(\eta_n^N(f)-\eta_n(f)\bigr)\Rightarrow
  N\bigl(0,\sigma_n^2(f)\bigr),\qquad
  \sigma_n^2(f)=\sum_{p=0}^n
  \frac{\eta_p\bigl([Q_{p,n}(f-\eta_nf)]^2\bigr)}{\eta_p(Q_{p,n}1)^2},$$
  and
  $$\sqrt N\left(\frac{\gamma_n^N(1)}{\gamma_n(1)}-1\right)\Rightarrow
  N\left(0,\sum_{p=0}^{n}\left[\frac{\eta_p\bigl((Q_{p,n}1)^2\bigr)}
  {\eta_p(Q_{p,n}1)^2}-1\right]\right).$$

* **60. Uniform-in-time particle approximation.** Suppose there are
  $\varepsilon_G,\varepsilon_M\in(0,1]$ such that, for all $n$ and all
  $x,x'$,
  $$G_n(x)\ge\varepsilon_GG_n(x'),\qquad
  M_n(x,\cdot)\ge\varepsilon_MM_n(x',\cdot).$$
  Then for every $p\ge1$ there is $c_p<\infty$ such that
  $$\sup_{n\ge0}\ \sup_{\mathop{\mathrm{osc}}(f)\le1}
  \sqrt N\,\Bigl(\mathbb E\bigl|\eta_n^N(f)-\eta_n(f)\bigr|^p\Bigr)^{1/p}
  \le\frac{c_p}{\varepsilon_M^2\varepsilon_G},$$
  where $\mathop{\mathrm{osc}}(f)=\sup f-\inf f$. The second hypothesis
  holds with $\varepsilon_M=a/b$ if
  $M_n(x,dy)=m_n(x,y)\,\lambda(dy)$ for a measure $\lambda$ and
  $a\le m_n\le b$ with constants $0<a\le b$.

A resampling step maps weighted particles $(x_i,w_i)$, with
$\sum_iw_i=1$, to $N$ equally weighted particles in which $x_i$ appears
$m_i$ times. It is **unbiased** if $\mathbb E[m_i\mid x,w]=Nw_i$.
**Multinomial resampling** draws $(m_i)$ from the multinomial law with
$N$ trials and probabilities $w_i$. **Residual resampling** keeps
$\lfloor Nw_i\rfloor$ copies of $x_i$ and allocates the remaining
$R=N-\sum_i\lfloor Nw_i\rfloor$ copies multinomially with probabilities
proportional to $Nw_i-\lfloor Nw_i\rfloor$. **Systematic resampling** uses
the single uniform $U$ and
$m_i=\lfloor N(w_1+\cdots+w_i)+U\rfloor-\lfloor N(w_1+\cdots+w_{i-1})+U\rfloor$.

* **61. Unbiased resampling and variance.** Multinomial, residual, and
  systematic resampling are unbiased, so the resampled average
  $N^{-1}\sum_im_if(x_i)$ has conditional mean $\sum_iw_if(x_i)$. Its
  conditional variance under multinomial resampling is
  $N^{-1}\mathop{\mathrm{Var}}_w(f)$, where
  $\mathop{\mathrm{Var}}_w(f)=\sum_iw_if(x_i)^2-(\sum_iw_if(x_i))^2$.
  Under residual resampling it is
  $RN^{-2}\mathop{\mathrm{Var}}_{\bar w}(f)$, where $\bar w$ are the
  normalized residual weights. Since $w$ is the mixture of the retained
  weights and $\bar w$ with weight $R/N$ on $\bar w$, this is never larger
  than the multinomial variance, for every $f$. For systematic resampling
  there are weights and functions $f$ for which the conditional variance
  exceeds the multinomial one. Item 58 holds for every unbiased
  resampling scheme.

### Variational data assimilation

Consider the **stochastic dynamics model**
$v_{j+1}=\Psi(v_j)+\xi_j$, $v_0\sim N(m_0,C_0)$, with observations
$y_{j+1}=h(v_{j+1})+\eta_{j+1}$, $j=0,\ldots,J-1$, where
$\xi_j\sim N(0,\Sigma)$, $\eta_{j+1}\sim N(0,\Gamma)$, $C_0,\Sigma,\Gamma>0$,
and all of these are independent. Write $|a|_C^2=a^\top C^{-1}a$ and, for a
path $v=(v_0,\ldots,v_J)$,
$$I(v;y)=\tfrac12|v_0-m_0|_{C_0}^2+\sum_{j=0}^{J-1}
\Bigl(\tfrac12|v_{j+1}-\Psi(v_j)|_\Sigma^2
+\tfrac12|y_{j+1}-h(v_{j+1})|_\Gamma^2\Bigr).$$
**Weak-constraint 4DVAR** minimizes $I(\cdot;y)$. **Strong-constraint
4DVAR** imposes the deterministic dynamics $v_{j+1}=\Psi(v_j)$ and minimizes
$I_{\det}(v_0;y)=\tfrac12|v_0-m_0|_{C_0}^2
+\sum_j\tfrac12|y_{j+1}-h(\Psi^{(j+1)}(v_0))|_\Gamma^2$
over the initial state only. For a fixed covariance $C>0$, **3DVAR** is
the filter in which $m_{j+1}$ is a minimizer of
$v\mapsto\tfrac12|v-\Psi(m_j)|_C^2+\tfrac12|y_{j+1}-h(v)|_\Gamma^2$.

* **62. 4DVAR as maximum a posteriori estimation.** The smoothing
  posterior of $v$ given $y$ has Lebesgue density proportional to
  $\exp(-I(v;y))$, and in the deterministic model the posterior of $v_0$
  has density proportional to $\exp(-I_{\det}(v_0;y))$. If $\Psi$ and $h$
  are continuously differentiable, each infimum is attained, and for all
  $u_1,u_2$
  $$\lim_{\delta\to0}\frac{\mathbb P(B(u_1,\delta)\mid y)}
  {\mathbb P(B(u_2,\delta)\mid y)}=\exp\bigl(I(u_2;y)-I(u_1;y)\bigr),$$
  with the analogous statement for $I_{\det}$. Thus the 4DVAR minimizers
  are exactly the posterior modes in the small-ball sense. For linear
  $\Psi$ and $h$ the posterior is Gaussian and the minimizer is the
  Kalman smoother mean.

<a id="synopsis-104c"></a>

## 104C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges

Let the forward diffusion on $[0,T]$ be
$$dX_t=f(t,X_t)\,dt+g(t)\,dW_t,$$
with $g(t)$ invertible, and write $p_t$ for the law of $X_t$. The **time
reversal** is $Y_t=X_{T-t}$.

* **63. Anderson's time reversal and the probability-flow equation.**
  Suppose $f$ is continuous and globally Lipschitz in $x$, uniformly in
  $t$, $g$ is continuous, and each $p_t$, $0<t\le T$, has a positive
  density, again written $p_t$, such that for all $t_0\in(0,T)$ and
  $r>0$
  $$\int_{t_0}^T\int_{\|x\|\le r}\bigl(p_t(x)^2+\|\nabla p_t(x)\|^2\bigr)
  \,dx\,dt<\infty,$$
  with $\nabla p_t$ the distributional gradient. Then (Haussmann–Pardoux)
  there is a Brownian motion $\bar W$ such that, on $[0,T)$,
  $$
  dY_t=\Bigl(-f(T-t,Y_t)+g(T-t)g(T-t)^\top\nabla\log p_{T-t}(Y_t)\Bigr)dt
  +g(T-t)\,d\bar W_t.
  $$
  The laws $q_t=p_{T-t}$ solve, in the sense of distributions on
  $(0,T)\times\mathbb R^d$, the continuity equation
  $\partial_tq_t+\nabla\cdot(q_tu_t)=0$ with
  $u_t=-f(T-t,\cdot)+\tfrac12g(T-t)g(T-t)^\top\nabla\log p_{T-t}$, the
  drift above with a factor $\tfrac12$ on the score term. If $u_t$ is
  globally Lipschitz in $x$, uniformly for $t\in[0,T']$, for every $T'<T$,
  and $X_0$ has finite second moment, then the solution of the probability-flow equation $\dot Z_t=u_t(Z_t)$
  with $Z_0\sim p_T$ has law $p_{T-t}$ for every $t<T$.

For a smooth positive density $q_\theta$ with the same support as a data
density $p$, the **Hyvärinen objective** is
$$\int\Bigl(\tfrac12\|\nabla\log q_\theta\|^2+\Delta\log q_\theta\Bigr)\,dp.$$

* **64. Score matching.** Suppose $p$ is positive on $\mathbb R^d$ and
  continuously differentiable,
  $q_\theta$ is twice continuously differentiable,
  $\|\nabla\log p\|^2$, $\|\nabla\log q_\theta\|^2$, and
  $|\Delta\log q_\theta|$ are $p$-integrable, and the vector field
  $p\nabla\log q_\theta$ is Lebesgue integrable. Then the Hyvärinen
  objective equals
  $\tfrac12\int\|\nabla\log q_\theta-\nabla\log p\|^2\,dp$ up to a constant
  free of $\theta$. If $Y=X+\sigma\varepsilon$ with $\varepsilon$ standard
  normal and independent of $X$, the regression target $-\varepsilon/\sigma=-(Y-X)/\sigma^2$
  has conditional expectation $\nabla\log p_\sigma(Y)$, where $p_\sigma$ is
  the law of $Y$. Hence, among measurable $s$ with
  $\mathbb E\|s(Y)\|^2<\infty$, the least-squares objective
  $\mathbb E\|s(Y)+\varepsilon/\sigma\|^2$ is minimized exactly by
  $s=\nabla\log p_\sigma$, $p_\sigma$-almost everywhere.

A **diffusion generative model** runs a forward noising process from the
data law toward a simple reference law, estimates the score along that
process, and generates a sample by the reverse equation of item 63, or by
its probability-flow equation, with the estimated score in place of
$\nabla\log p_t$.

* **65. Generation by a learned reversal.** For $k\ge1$ let $s^{(k)}$ and
  $\eta_k$ be estimated scores and initial laws satisfying the hypotheses
  of item 68, and let $Q^{(k)}$ be the corresponding learned reverse path
  laws. If $\mathop{\mathrm{KL}}(p_T\|\eta_k)\to0$ and
  $\int_0^T\mathbb E_{p_t}\|g(t)^\top(s^{(k)}_t-\nabla\log p_t)\|^2\,dt\to0$
  as $k\to\infty$, then the law of the endpoint of $Q^{(k)}$ at reverse
  time $T$ converges in total variation to $p_0$, the law of $X_0$.

Let $R$ be the path law of Brownian motion with a specified initial
probability, or another specified Markov reference, on $C([0,T];\mathbb R^d)$,
and write $R_{0T}$ for its joint law at times $0$ and $T$. The
**Schrödinger bridge** from $\mu_0$ to $\mu_T$ is the path measure of
minimum Kullback–Leibler divergence from $R$ among path measures with
those endpoint marginals.

* **66. Schrödinger bridge.** Suppose a finite-entropy feasible path
  law exists. The bridge is unique and reduces to minimizing
  $\mathop{\mathrm{KL}}(\gamma\|R_{0T})$ over couplings of the prescribed
  endpoints. Given those endpoints its conditional path law is that of
  the reference bridge. For Brownian motion with initial density $r_0$,
  $R_{0T}(dx,dy)=r_0(x)q_T(y-x)\,dx\,dy$ with
  $q_T(z)=(2\pi T)^{-d/2}e^{-\|z\|^2/(2T)}$. If $\mu_0,\mu_T$ have
  densities and finite second moments, with
  $\mathop{\mathrm{KL}}(\mu_0\|r_0)<\infty$ and
  $\int\mu_T|\log\mu_T|<\infty$, then for every coupling
  $\gamma\in\Pi(\mu_0,\mu_T)$
  $$\mathop{\mathrm{KL}}(\gamma\|R_{0T})=\int\frac{\|x-y\|^2}{2T}\,d\gamma
  +\mathop{\mathrm{KL}}(\gamma\|\mu_0\otimes\mu_T)+c,$$
  where $c=\mathop{\mathrm{KL}}(\mu_0\|r_0)+\int\mu_T\log\mu_T
  +\tfrac d2\log(2\pi T)$ depends only on the marginals.

Let $(X_0,X_1)$ be a coupling of $\mu_0$ and $\mu_1$, and let
$v_t(x\mid x_0,x_1)$ be a conditional velocity whose flow carries $x_0$ to
$x_1$. **Flow matching** regresses a time-dependent vector field against
that conditional velocity.

* **67. Marginal velocity.** Let $X_t=\psi_t(X_0,X_1)$, $t\in[0,1]$, where
  $t\mapsto\psi_t(x_0,x_1)$ is continuously differentiable, $\psi_0(x_0,x_1)=x_0$,
  $\psi_1(x_0,x_1)=x_1$, and $\int_0^1\mathbb E\|\dot X_t\|^2\,dt<\infty$.
  Among measurable $u$ with $\int_0^1\mathbb E\|u_t(X_t)\|^2dt<\infty$,
  the objective $\int_0^1\mathbb E\|u_t(X_t)-\dot X_t\|^2\,dt$ is minimized
  by
  $$v_t(x)=\mathbb E[\dot X_t\mid X_t=x].$$
  The law $\mu_t$ of $X_t$ satisfies
  $\partial_t\mu_t+\nabla\cdot(\mu_t v_t)=0$ in the sense of distributions
  on $(0,1)\times\mathbb R^d$. If moreover $v_t$ is globally Lipschitz in
  $x$, uniformly in $t\in[0,1]$, and $\mu_0$ has finite first moment,
  then the flow of $\dot z=v_t(z)$ carries $\mu_0$ to $\mu_t$ for every
  $t$, in particular to $\mu_1$.

* **68. Score error and total variation.** Assume the hypotheses of the
  first part of item 63, and let $P$ be the path law of the exact
  reversal $(Y_t)_{0\le t\le T}$. Let $s_t(x)$ be an estimated score,
  measurable in $(t,x)$ and globally Lipschitz in $x$ uniformly in $t$,
  and let $Q$ be the law of the solution of
  $dY_t=\bigl(-f(T-t,Y_t)+g(T-t)g(T-t)^\top s_{T-t}(Y_t)\bigr)dt
  +g(T-t)\,d\bar W_t$ with initial law $\eta$. If
  $\mathop{\mathrm{KL}}(p_T\|\eta)<\infty$ and the weighted score error
  is bounded,
  $$\sup_{0<t\le T,\;x\in\mathbb R^d}
  \|g(t)^\top(s_t(x)-\nabla\log p_t(x))\|<\infty,$$
  then
  $$\mathop{\mathrm{KL}}(P\|Q)
  \le\mathop{\mathrm{KL}}(p_T\|\eta)
  +\frac12\int_0^T\mathbb E_{p_t}
  \|g(t)^\top(s_t-\nabla\log p_t)\|^2\,dt.$$
  Since marginalization cannot increase KL, Pinsker's inequality gives
  that the total variation distance between $p_0$ and the law of the
  endpoint of $Q$ is at most $\sqrt{\mathop{\mathrm{KL}}(P\|Q)/2}$.

### Gaussian noising, endpoint constraints, and interpolants

* **69. Tweedie's denoising identity.** Let $Y=X+\sigma\varepsilon$,
  $\sigma>0$, with independent standard Gaussian $\varepsilon$ and
  $X\in L^2$. For the positive smoothed density $p_\sigma$,
  $$\mathbb E[X\mid Y=y]=y+\sigma^2\nabla\log p_\sigma(y).$$
  Differentiating the Gaussian convolution also gives
  $$\mathop{\mathrm{Cov}}(X\mid Y=y)
  =\sigma^2I+\sigma^4\nabla^2\log p_\sigma(y).$$

* **70. Gaussian diffusion marginals.** For the forward chain
  $Z_t=\sqrt{1-\beta_t}Z_{t-1}+\sqrt{\beta_t}\xi_t$,
  with independent standard normal noises and $0<\beta_t<1$, put
  $\bar\alpha_t=\prod_{s=1}^t(1-\beta_s)$. Then
  $$Z_t\mid Z_0=x\sim
  N(\sqrt{\bar\alpha_t}x,(1-\bar\alpha_t)I).$$
  The population squared-error minimizer for predicting the aggregate
  standard normal noise $\varepsilon$ from $Z_t$ is
  $\mathbb E[\varepsilon\mid Z_t]$. Multiplying it by
  $-1/\sqrt{1-\bar\alpha_t}$ gives the marginal score at time $t$.

* **71. Endpoint potentials and entropy projection.** Let $P^*$ be a path
  law with endpoint marginals $\mu_0,\mu_T$ and
  $$\frac{dP^*}{dR}=f(X_0)g(X_T)$$
  for measurable $f,g>0$ with $\log f\in L^1(\mu_0)$ and
  $\log g\in L^1(\mu_T)$. Then for every path law $Q$ with marginals
  $\mu_0,\mu_T$ and $\mathop{\mathrm{KL}}(Q\|R)<\infty$,
  $$\mathop{\mathrm{KL}}(Q\|R)
  =\mathop{\mathrm{KL}}(Q\|P^*)+
  \mathop{\mathrm{KL}}(P^*\|R),$$
  so $P^*$ is the Schrödinger bridge of item 66. If $R_{0T}$ is
  equivalent to $R_0\otimes R_T$ and $f'(X_0)g'(X_T)$, with $f',g'>0$, is
  another such density, then $f'=cf$ $\mu_0$-almost everywhere and
  $g'=g/c$ $\mu_T$-almost everywhere for a constant $c>0$.

* **72. Straight interpolants and transport action.** For any coupling
  of square-integrable endpoints, put $X_t=(1-t)X_0+tX_1$ and
  $v_t(x)=\mathbb E[X_1-X_0\mid X_t=x]$. Then
  $$W_2^2(\mu_0,\mu_1)\le
  \int_0^1\mathbb E\|v_t(X_t)\|^2dt
  \le\mathbb E\|X_1-X_0\|^2.$$
  The right inequality is conditional Jensen; the left is the
  dynamic transport bound for the induced continuity equation of item 67.
  If the coupling is optimal for the quadratic cost, both inequalities are
  equalities and the laws of $X_t$ form the displacement interpolation of
  CKMA SYNOPSIS39, item 48.

### Training objectives and discrete-time samplers

For the forward diffusion of item 63, let $p_{t|0}(x\mid x_0)$ be its
transition density from time $0$. For a drift $f(t,x)=a(t)x$ with scalar
continuous $a$ and scalar continuous nonzero $g$, as in the usual
isotropic noising processes,
$X_t\mid X_0\sim N(A_tX_0,\sigma_t^2I)$ for deterministic $A_t$ and
$\sigma_t>0$, and $\nabla_x\log p_{t|0}(X_t\mid X_0)=-Z/\sigma_t$ where
$X_t=A_tX_0+\sigma_tZ$.
Here $A_t=\exp(\int_0^t a(s)\,ds)I$ and
$\sigma_t^2=\int_0^t\exp(2\int_s^t a(u)\,du)g(s)^2\,ds$.
A general affine matrix drift instead gives an affine conditional mean
and a matrix covariance; the isotropic formula is not asserted for it.

* **73. Denoising score matching along a diffusion.** Fix $t>0$, suppose
  $p_t$ is smooth and positive, and suppose
  $\mathbb E\|\nabla_x\log p_{t|0}(X_t\mid X_0)\|^2<\infty$. Then for every
  measurable $s$ with $\mathbb E\|s(X_t)\|^2<\infty$,
  $$\mathbb E\|s(X_t)-\nabla\log p_t(X_t)\|^2
  =\mathbb E\|s(X_t)-\nabla_x\log p_{t|0}(X_t\mid X_0)\|^2-C_t,$$
  where $C_t=\mathbb E\|\nabla_x\log p_{t|0}(X_t\mid X_0)
  -\nabla\log p_t(X_t)\|^2$ does not depend on $s$. The identity is the
  Pythagorean relation for the conditional expectation
  $\nabla\log p_t(X_t)=\mathbb E[\nabla_x\log p_{t|0}(X_t\mid X_0)\mid X_t]$,
  which extends item 64 to every noising kernel. Integrating against a
  weight $w(t)\ge0$ gives a regression objective whose excess risk is the
  time-integrated score error of item 68 when $w=g^2$ for scalar $g$.
  In the Gaussian case $C_t\le d/\sigma_t^2$, and with the weight
  $w(t)=\sigma_t^2$ the integrand becomes the noise-prediction loss
  $\mathbb E\|\sigma_ts(X_t)+Z\|^2$.

* **74. Gaussian reverse conditionals and the diffusion evidence bound.**
  In the chain of item 70, with $\bar\alpha_0=1$ and $t\ge2$,
  $$Z_{t-1}\mid(Z_t,Z_0=x)\sim N\bigl(m_t(x,Z_t),s_t^2I\bigr),\quad
  m_t=\frac{\sqrt{1-\beta_t}\,(1-\bar\alpha_{t-1})Z_t
  +\sqrt{\bar\alpha_{t-1}}\,\beta_tx}{1-\bar\alpha_t},\quad
  s_t^2=\frac{\beta_t(1-\bar\alpha_{t-1})}{1-\bar\alpha_t}.$$
  For a reverse model $p_\theta(z_T)\prod_tp_\theta(z_{t-1}\mid z_t)$,
  $$-\log p_\theta(x)\le
  \mathbb E[-\log p_\theta(x\mid Z_1)]
  +\sum_{t=2}^T\mathbb E\,\mathop{\mathrm{KL}}\bigl(q(\cdot\mid Z_t,x)\,\|\,
  p_\theta(\cdot\mid Z_t)\bigr)
  +\mathop{\mathrm{KL}}\bigl(q(Z_T\mid x)\,\|\,p_\theta(Z_T)\bigr),$$
  where $q$ is the forward chain started at $x$; this is the evidence
  lower bound of item 25, for the latent path. If
  $p_\theta(\cdot\mid z_t)=N(\mu_\theta(z_t,t),s_t^2I)$ and
  $\mu_\theta=(1-\beta_t)^{-1/2}\bigl(z_t-\beta_t(1-\bar\alpha_t)^{-1/2}
  \varepsilon_\theta(z_t,t)\bigr)$, then the $t$-th term equals
  $$\frac{\beta_t^2}{2s_t^2(1-\beta_t)(1-\bar\alpha_t)}\,
  \mathbb E\|\varepsilon-\varepsilon_\theta(Z_t,t)\|^2,
  \qquad Z_t=\sqrt{\bar\alpha_t}\,x+\sqrt{1-\bar\alpha_t}\,\varepsilon.$$
  Dropping these weights gives the usual noise-prediction objective,
  a weighted sum of the denoising score matching losses of item 73 at
  discrete noise levels.

Consider the variance-exploding forward process $dX_t=dW_t$, $X_0\sim\pi$,
so $\pi_t=\pi*N(0,tI)$. Let $0=\tau_0<\cdots<\tau_N<T$ with steps
$h_n=\tau_{n+1}-\tau_n$, put $\delta=T-\tau_N$, and let $\hat s_t$ be a
score estimate. The **DDPM sampler** starts from $\hat X_0\sim N(0,TI)$ and
sets
$$\hat X_{\tau_{n+1}}=\hat X_{\tau_n}+h_n\hat s_{T-\tau_n}(\hat X_{\tau_n})
+\sqrt{\frac{(T-\tau_{n+1})h_n}{T-\tau_n}}\,\xi_{n+1},$$
with independent standard normal $\xi_n$, which freezes the denoiser of
item 69 on each step.

* **75. Convergence of diffusion sampling under a second-moment
  assumption.** Suppose only that $m_2^2=\mathbb E_\pi\|X\|^2<\infty$, and
  that $h_n\le\bar h(T-\tau_n)$ with $\bar h\le1/2$. Put
  $\varepsilon_{\mathrm{sc}}^2=\sum_nh_n\mathbb E_{\pi_{T-\tau_n}}
  \|\hat s_{T-\tau_n}-\nabla\log\pi_{T-\tau_n}\|^2$. Then the law
  $\hat\pi$ of $\hat X_{\tau_N}$ satisfies
  $$\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\le\frac{m_2^2}{2T}
  +4\varepsilon_{\mathrm{sc}}^2+2\bar h\,d\bigl(1+\log(T/\delta)\bigr),$$
  the three terms being initialization, score, and discretization error.
  Given $0<\delta<T$ and $\bar h\le1/2$, let $N$ be the least integer with
  $(1-\bar h)^NT\le\delta$, take $h_n=\bar h(T-\tau_n)$ for $n<N-1$ and
  $h_{N-1}=T-\tau_{N-1}-\delta$; these steps satisfy the hypothesis and
  $N\le1+\bar h^{-1}\log(T/\delta)$. Hence, for $0<\varepsilon^2\le d$,
  taking $T=m_2^2/\varepsilon^2>\delta$ and
  $\bar h=\varepsilon^2/(2d(1+\log(T/\delta)))$ gives
  $\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\le\tfrac32\varepsilon^2
  +4\varepsilon_{\mathrm{sc}}^2$ with
  $N\le1+2d\varepsilon^{-2}(1+\log(T/\delta))\log(T/\delta)$ steps. No
  log-concavity, functional inequality, or density of $\pi$ is required,
  and $W_2(\pi,\pi_\delta)\le\sqrt{\delta d}$.

### Marginal-preserving dynamics and bridge iterations

* **76. A family of diffusions with prescribed marginals.** Let $\mu_t$,
  $t\in[0,1]$, be smooth positive densities solving
  $\partial_t\mu_t+\nabla\cdot(\mu_tv_t)=0$, and let $\epsilon_t\ge0$ be
  continuous. Then $\mu_t$ also solves the Fokker–Planck equation of
  $$dX_t=\bigl(v_t+\epsilon_t\nabla\log\mu_t\bigr)(X_t)\,dt
  +\sqrt{2\epsilon_t}\,dW_t,$$
  because $\epsilon_t\nabla\cdot(\mu_t\nabla\log\mu_t)=\epsilon_t\Delta\mu_t$.
  If the drift $b_t=v_t+\epsilon_t\nabla\log\mu_t$ is globally Lipschitz
  in $x$, uniformly in $t\in[0,1]$, and
  $\int_0^1\int\|b_t\|\,d\mu_t\,dt<\infty$, then $X_0\sim\mu_0$ gives
  $X_t\sim\mu_t$ for all $t$; the same holds in reverse time with drift
  $v_t-\epsilon_t\nabla\log\mu_t$ under the same hypotheses on that drift.
  For a
  forward diffusion with scalar $g$, the choices $\epsilon=0$ and
  $\epsilon=g^2/2$ with $v_t=f-\tfrac12g^2\nabla\log p_t$ recover the
  probability-flow equation and the original diffusion of item 63. For a
  **stochastic interpolant** $X_t=I_t(X_0,X_1)+\gamma_tZ$, with
  $I_0(x_0,x_1)=x_0$, $I_1(x_0,x_1)=x_1$, $\gamma_0=\gamma_1=0$,
  $\gamma_t>0$ on $(0,1)$, $I$ and $\gamma$ continuously differentiable in
  $t$ with $\int_0^1\mathbb E\|\partial_tI_t(X_0,X_1)\|^2dt<\infty$ and
  $\int_0^1\dot\gamma_t^2dt<\infty$, and $Z$ standard normal independent of the
  coupling,
  $$v_t(x)=\mathbb E[\partial_tI_t(X_0,X_1)+\dot\gamma_tZ\mid X_t=x],\qquad
  \nabla\log\mu_t(x)=-\gamma_t^{-1}\mathbb E[Z\mid X_t=x],$$
  so velocity and score are both population least-squares regressions, as
  in item 67; here $\mu_t$ is the law of $X_t$, which has a smooth
  positive density for $0<t<1$. Flow matching is the case $\gamma=0$ of
  the velocity regression.

For path measures $Q,R$ on $C([0,T];\mathbb R^d)$, write $Q_0,Q_T$ for the
endpoint laws and $Q^x$ for a regular conditional law of $Q$ given
$X_0=x$. The **half-bridge** problems minimize $\mathop{\mathrm{KL}}(Q\|P)$
over $Q$ with one prescribed endpoint law. **Iterative proportional
fitting** sets $P^0=R$ and alternately takes $P^{2k+1}$ to be the
half-bridge from $P^{2k}$ with terminal law $\mu_T$ and $P^{2k+2}$ the
half-bridge from $P^{2k+1}$ with initial law $\mu_0$.

* **77. Half-bridges and iterative proportional fitting.** The chain
  rule
  $\mathop{\mathrm{KL}}(Q\|P)=\mathop{\mathrm{KL}}(Q_0\|P_0)
  +\int\mathop{\mathrm{KL}}(Q^x\|P^x)\,Q_0(dx)$
  shows that if $\mathop{\mathrm{KL}}(\mu_0\|P_0)<\infty$, the unique
  half-bridge with initial law $\mu_0$ is
  $\int P^x\,\mu_0(dx)=\frac{d\mu_0}{dP_0}(X_0)\cdot P$, with value
  $\mathop{\mathrm{KL}}(\mu_0\|P_0)$; similarly, if
  $\mathop{\mathrm{KL}}(\mu_T\|P_T)<\infty$, the unique half-bridge with
  terminal law $\mu_T$ is $\frac{d\mu_T}{dP_T}(X_T)\cdot P$. Every
  iterate therefore has the form $f_k(X_0)g_k(X_T)\cdot R$, keeps the
  reference bridges of item 66, and has endpoint couplings equal to the
  Sinkhorn iterates for the kernel $R_{0T}$, CKMA SYNOPSIS39, item 90.
  If $P^*$ is the Schrödinger bridge of item 66 with
  $\mathop{\mathrm{KL}}(P^*\|R)<\infty$, then each half-step is an entropy
  projection onto a linear family containing $P^*$, so
  $$\mathop{\mathrm{KL}}(P^*\|P^k)=\mathop{\mathrm{KL}}(P^*\|P^{k+1})
  +\mathop{\mathrm{KL}}(P^{k+1}\|P^k),$$
  as in item 71. Hence $\mathop{\mathrm{KL}}(P^*\|P^k)$ is nonincreasing
  and $\sum_k\mathop{\mathrm{KL}}(P^{k+1}\|P^k)\le\mathop{\mathrm{KL}}(P^*\|R)$.
  The endpoint marginals of $P^k$ therefore converge to $\mu_0$ and
  $\mu_T$ in relative entropy and in total variation. If moreover
  $R_{0T}\ll\mu_0\otimes\mu_T$ with density $e^{-c}$, where $c$ is
  bounded below and $\int e^{rc}\,d(\mu_0\otimes\mu_T)<\infty$ for some
  $r>1$, then $\mathop{\mathrm{KL}}(P^*\|P^k)\to0$, so the endpoint
  couplings of $P^k$ converge in total variation to the endpoint
  coupling of $P^*$. Without some such condition on the reference,
  convergence of the couplings is not asserted here.

## Reference guide

### Correspondence with the subdivisions

- **[104A](#synopsis-104a)**: Jeffreys, Box and Tiao, Berger, Robert, Ghosh,
  Delampady, and Samanta, and Gelman, Carlin, Stern, Dunson, Vehtari, and
  Rubin carry conjugate analysis, invariant priors, the Laplace expansion, and
  the Bernstein–von Mises theorem. Giné and Nickl, and Nickl's Zurich
  lectures, carry posterior contraction and Bayesian inverse problems. The
  Dirichlet process and the general contraction theorem are the theorems of
  Ferguson, Sethuraman, Doob, Schwartz, and Ghosal, Ghosh, and van der Vaart.
- **[104B](#synopsis-104b)**: Robert's computational chapters, Del Moral,
  Douc, Moulines, Priouret, and Soulier, Meyn and Tweedie, and Levin, Peres,
  and Wilmer carry importance sampling and Markov chain Monte Carlo.
  Wainwright and Jordan carry the evidence lower bound. Robert and Casella,
  Liu, and Hammersley and Handscomb carry exact simulation, variance
  reduction, convergence of Metropolis–Hastings and Gibbs samplers, the slice
  sampler, and hybrid Monte Carlo. Jordan, Kinderlehrer, and Otto, and Figalli
  and Glaudo, carry the minimizing-movement scheme. Pavliotis carries the
  Langevin diffusion. Chewi's manuscript carries non-asymptotic bounds for its
  discretization. Kushner and Yin, and Borkar, carry stochastic approximation
  and averaging. Ambrosio, Gigli, and Savaré carry the gradient-flow
  identification already numbered in CKMA SYNOPSIS39. Sznitman carries
  propagation of chaos. Carmona and Delarue carry mean-field games and
  interacting diffusions. Del Moral carries Feynman–Kac particle systems. Mei,
  Montanari, and Nguyen, and Chizat and Bach, carry the mean-field limit of
  two-layer networks.
- **[104C](#synopsis-104c)**: Hyvärinen carries score matching. Vincent
  carries denoising score matching. Song, and Ho, Jain, and Abbeel, carry
  diffusion generative models. Léonard, and Peyré and Cuturi, carry the
  Schrödinger bridge. Lipman, Chen, Ben-Hamu, Nickel, and Le carry flow
  matching.

### Source comparisons and local copies

#### Bayesian statistics and Monte Carlo methods

Ghosh, Delampady, and Samanta, Sections 2.6–2.8, were consulted for
posterior propriety, posterior loss minimization, Bayes factors, and
prediction. Robert–Casella, Chapters 3–4, supplies importance sampling
and conditional Monte Carlo; its full text is in `ReferencesSuppl`.
For item 1, van der Vaart's Theorem 10.1 gives quadratic-mean
differentiability and uniformly consistent separation tests, rather than
posterior consistency alone. Ghosal–van der Vaart's Theorem 8.9, also
read in a supplemental local copy, supplies the half-radius entropy
condition and the sieve-tail exponent $C+4$ used in item 19. Item 20 is
the sequence-space form of the theorem of Knapik, van der Vaart, and van
Zanten, with the minimax rate surveyed by Cavalier; neither was consulted
locally. The uniformity over $S^\beta(R)$ follows from the explicit
Gaussian posterior mean and covariance.

Item 5 is the Laplace expansion used by Ghosh, Delampady, and Samanta and by
Robert. Item 19 uses a standard sufficient contraction criterion with
sieve-tail exponent $C+4$, consistent with the local Ghosal–van der Vaart
treatment. Items 22 and 23 are the invariance statements of the Monte Carlo
texts. Item 24 invokes the geometric
ergodicity criterion already numbered in the analysis synopsis.

Berger's Sections 4.3.2–4.3.3 and 4.5.2–4.5.4
supply highest posterior density sets, the point-null Bayes factor
(4.17) with the lower bound of Theorem 1 in Section 4.3.3, the normal-means
empirical Bayes estimates (4.33)–(4.35), and Robbins' Poisson estimator
(Example 16). Robert's Definition 5.5.2, Lemma 10.4.2, and Examples 10.4.1
and 10.5.1 supply the volume property of highest posterior density
regions, the exponential-family posterior-mean identity, and the empirical
Bayes reading of the James–Stein estimator. Ghosh, Delampady, and Samanta,
Section 6.4, were read for the Jeffreys–Lindley paradox, and Gelman et
al., Section 5.4, equations (5.17)–(5.21), for the hierarchical normal
model; the propriety threshold $J\ge3$ for the flat prior on $\tau$ in item 12 follows from the tail $\tau^{1-J}$ of (5.21). Ghosal–van der Vaart,
Section 4.1.4, Proposition 4.8, and Section 4.2.4 supply item 16. In
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
they are not part of the consulted source basis. The consulted
supplemental copies of Ghosal–van der Vaart and Robert–Casella are linked
below.

#### Stochastic dynamics for data

Chewi's local 2026 manuscript, Theorem 4.3.6, gives an entropy
guarantee for a mixture of iterate laws, with square-root KL bounded by
$\varepsilon$; it is not a guarantee for the law of the arithmetic average.
The Gaussian covariance calculation in item 42 gives an exact example
of discretization bias. Pavliotis supplies the invariant-density and entropy
framework; Kushner–Yin and Borkar supply stochastic approximation. The
minus sign in the recursion makes positive real parts of $Dh$ the stable
case. Nonnegative radial drift without attraction is insufficient.
The original paper of Polyak and Juditsky (SIAM J. Control Optim. 30,
1992) could not be accessed. The averaging statement in item 40 was
checked against Theorem B.1 of
[Cutler, Díaz, and Drusvyatskiy, *Stochastic approximation with
decision-dependent distributions*](https://arxiv.org/abs/2207.04173),
Appendix B, a variant of Polyak and Juditsky's Theorem 2 with explicit
hypotheses: martingale-difference noise bounded in $L^2$, Cesàro
convergence in probability of the conditional covariances, a conditional
Lindeberg condition, steps with $(a_n-a_{n+1})/a_n=o(a_n)$, a positively
stable $A$, and
$n^{-1/2}\sum_{k<n}\|h(\theta_k)-A(\theta_k-\theta^\star)\|\to0$ in
probability. The hypotheses of item 40 imply these: the
$(2+\delta)$-moment bound gives the Lindeberg condition, the
convergence of the bounded conditional covariances gives their Cesàro
convergence, strong monotonicity makes $A$ positively stable, and the
locally Lipschitz derivative together with global Lipschitz continuity
gives $\|h(\theta)-A(\theta-\theta^\star)\|\le C\|\theta-\theta^\star\|^2$,
so the last condition follows from the standard mean-square bound
$\mathbb E\|\theta_n-\theta^\star\|^2=O(a_n)$ and $\alpha>1/2$.

Law–Stuart–Zygalakis was found in `ReferencesSuppl`; Sections 4.2.3–4.2.4
were read for perturbed-observation and square-root ensemble updates.
The distinction from exact nonlinear filtering is explicit there. The
large-ensemble limit in item 52 is Theorem 5.1 of
[Le Gland, Monbet, and Tran, *Large sample asymptotics for the ensemble
Kalman filter*, INRIA report RR-7014, 2009](https://inria.hal.science/inria-00409060),
which allows additive Gaussian model noise and a globally Lipschitz drift
(their Assumption A) and gives almost sure convergence of empirical
averages of locally Lipschitz test functions of polynomial growth; the
functions $x$ and $xx^\top$ give the mean and covariance, and in the
linear case the limit is the Kalman filter, as stated in their abstract
and Section 2.1.
[Mandel, Cobb, and Beezley, *On the convergence of the ensemble Kalman
filter*](https://arxiv.org/abs/0901.2951), Theorem 1 and Corollary 1,
give convergence in every $L^p$ for an affine model without model noise.
The covariance identity for $\eta_i=0$ is algebra.
Item 53 is stated for the square loss, where the particle system is a
deterministic interacting system with Lipschitz interaction and the limit
follows from Dobrushin's stability estimate in $W_1$.
Del Moral's 2013 volume treats Feynman–Kac measures, unbiased unnormalized
particle estimates, and particle normalizing constants. Items 57 and 58 use
fixed observations and average over particle randomness. Finite-time
propagation of chaos requires an initial independence or chaos hypothesis;
neither it nor a finite-time training limit implies a global convergence
or uniform-time theorem.

For item 54, [Liu and Wang's original paper](https://papers.neurips.cc/paper_files/paper/2016/hash/b3ba8f1bee1238a2f37603d90b58898d-Abstract.html)
was read for the transport derivative and kernel velocity. The smooth-law
variational calculation does not differentiate the infinite KL divergence
of an empirical atomic measure from a continuous target.

Bishop–Bishop, Chapter 20, especially Sections 20.2–20.3, was read for
Gaussian diffusion marginals, denoising scores, and reverse SDEs.
The noise target in item 64 is $-\varepsilon/\sigma$ when
$Y=X+\sigma\varepsilon$. Item 69 follows by differentiating that Gaussian
convolution. The endpoint error in item 68 is the Girsanov entropy
identity and marginal contraction; it includes initialization, weighted
time-integrated score error, and absolute continuity. No automatic
polynomial dimension bound is asserted. The time-reversal hypotheses of
item 63 are those of Haussmann and Pardoux (Ann. Probab. 14, 1986,
Theorem 2.1), whose paper could not be accessed; they were checked
against the restatement in Section 4 of
[Raginsky, *A variational approach to sampling in diffusion
processes*](https://arxiv.org/abs/2405.00126): global Lipschitz and
linear-growth bounds on drift and diffusion coefficient, and
$\int_{t_0}^T\int_A(p^2+\|\sigma^\top\nabla p\|^2)<\infty$ for all
$t_0\in(0,T)$ and bounded open $A$. With $g(t)$ continuous and
invertible the weight $\sigma^\top=g^\top$ may be dropped. The
probability-flow statement uses uniqueness for continuity equations with
Lipschitz velocity, as in Ambrosio, Gigli, and Savaré, Proposition 8.1.8.
For item 68, Chewi, proof of Theorem 12.3.2, and
[Chen, Chewi, Li, Li, Salim, and Zhang, *Sampling is as easy as learning
the score*](https://arxiv.org/abs/2209.11215), Section 5, were read. Both
combine the chain rule for relative entropy with Girsanov's theorem;
Chewi omits the verification that the exponential martingale is a true
martingale, and Chen and coauthors supply it by an approximation
argument only for their discretized Ornstein–Uhlenbeck scheme with a
Lipschitz true score (proof of their Theorem 9). Item 68 therefore
assumes a bounded weighted score error, under which Novikov's criterion
holds and the bound follows from Le Gall, *Brownian Motion, Martingales,
and Stochastic Calculus*, Theorems 5.22 and 5.23, with uniqueness in law
for the Lipschitz learned reverse equation; it then holds with equality.

Peyré–Cuturi's Schrödinger discussion distinguishes static endpoint
coupling from reference conditional bridges. Item 66 specifies the
Brownian noise normalization and initial reference law. The conditional
expectation in flow matching gives a continuity equation; a deterministic
ODE representation needs well-posedness. The straight-interpolant action
bound in item 72 is also a direct consequence of conditional Jensen and
CKMA SYNOPSIS39, items 48–49.

Evensen's book and the original papers of Song, Ho–Jain–Abbeel, and
Lipman and coauthors were not located locally. Their diffusion framework
is treated in the consulted Bishop–Bishop text. Del Moral's 2013 volume
is in `References`; his 2004 Feynman–Kac monograph is in `ReferencesSuppl`
and supplies the Feynman–Kac results below.

For 104B, Chewi's manuscript was read in Theorems 1.2.21–1.2.26 (Poincaré
and $\chi^2$ decay, logarithmic Sobolev and KL decay; item 44), Theorems
4.1.2 and 4.2.7 (coupling bias and the Vempala–Wibisono bound; item 45),
Section 10.1 and display (10.1.1) (stochastic-gradient Langevin; item 46),
Theorems 7.3.4, 7.3.5, and 7.6.5 with the bibliographical notes to Chapter 7
(MALA; item 47), and Section 5.3, Theorems 5.3.6, 5.3.14, and 5.3.15
(kinetic Langevin; item 48). Chewi's display (10.1.1) is derived
informally, so the bound in item 46 is instead Theorem 4 (with zero bias,
$\delta=0$) of
[Dalalyan and Karagulyan, *User-friendly guarantees for the Langevin Monte
Carlo with inaccurate gradient*](https://arxiv.org/abs/1710.00095),
Stoch. Proc. Appl. 129 (2019); their variance parameter is normalized
per coordinate, so their $\sigma^2$ is $\sigma^2/d$ here. The warm-start
upper and lower bounds in item 47 are Theorems 1 and 2 of
[Wu, Schmidler, and Chen, *Minimax mixing time of the Metropolis-adjusted
Langevin algorithm for log-concave sampling*](https://arxiv.org/abs/2109.13055),
JMLR 23 (2022), stated there for the $\tfrac12$-lazy chain and for
warmness in the sense of a bounded density ratio; Chewi's Theorems 7.3.5
and 7.6.5 summarize them. Theorem 3 of
[Chewi, Lu, Ahn, Cheng, Le Gouic, and Rigollet, *Optimal dimension
dependence of the Metropolis-adjusted Langevin algorithm*](https://arxiv.org/abs/2012.12810)
gives the earlier warm-start bound $\beta^{4/3}d^{1/2}\alpha^{-3/2}$ up to
logarithms of $d\kappa M/\varepsilon$. The cold-start statement is Chewi's
Theorem 7.3.4, whose $\tilde O$ suppresses factors polylogarithmic in
$\kappa d$ and whose accuracy dependence is polylogarithmic in
$1/\varepsilon$. In item 48, Theorem 5.3.14 gives a rate constant
depending only on $c_0$ with a universal prefactor, and Theorem 5.3.15 a
universal rate constant $c'$; the coefficients $a,b,c$ of its Lyapunov
functional are not specified in the statement. Robert and Casella, Section 7.8, was read for
the acceptance rates $0.234$ and $0.574$; the papers of Roberts, Gelman, and
Gilks and of Roberts and Rosenthal are not available locally. Figalli–Glaudo,
Section 3.3, was read for the JKO scheme on bounded convex domains; the
whole-space hypotheses of item 43 are those of the original JKO paper, which
is not local. Borkar's second edition, Chapter 2 (assumptions (A1)–(A4),
Theorem 2.1, Corollaries 2.1–2.2) and Chapter 4 (assumption (A9), Theorem 4.1),
was read for items 49 and 50, with the signs converted to the convention of item 40.

For 104B, Del Moral's 2004 monograph (local in `ReferencesSuppl`) was read in
Chapter 9, Theorem 9.3.1, Corollary 9.3.1, and Propositions 9.4.1–9.4.2, for
the fluctuation variances in item 59, which are specialized here to
multinomial selection, and in Theorem 7.4.4 with conditions (G) and $(M)_m$
of Section 4.4, for item 60 with $m=1$. Liu, Section 3.4, and Robert–Casella,
Section 14.3.5, were read for residual and systematic resampling; the
variance comparison in item 61 is the law of total variance. Law, Stuart, and
Zygalakis, Theorems 2.8, 2.11, 3.10, and 3.12 and Section 4.2.1, were read for
item 62.

For 104C, Chewi, Chapter 12 (Sections 12.1–12.3, Theorem 12.3.2 and Lemma
12.3.3), was read for items 73, 75, and 76, including the denoising
identity, the probability-flow variants, and the stochastic-interpolant
regression. Bishop–Bishop, Sections 20.1.2 and 20.2.2–20.2.4, was read for
item 74. Item 77 uses the chain rule for relative entropy and the projection
identity of item 71. Its convergence statements were checked in
[Nutz, *Introduction to Entropic Optimal Transport*, lecture notes,
Columbia University, 2021](https://www.math.columbia.edu/~mnutz/docs/EOT_lecture_notes.pdf),
Section 6: Corollary 6.6 gives the convergence of the marginals in
relative entropy with no further condition, and Theorem 6.15(iii) gives
$\mathop{\mathrm{KL}}(\pi^*\|\pi_t)\to0$ and convergence in variation of
the couplings under the stated lower bound and exponential integrability
of $c$. Nutz, Remark 6.17, records that Rüschendorf's convergence theorem
(Ann. Statist. 23, 1995, not accessed) also needs additional integrability
conditions; finiteness of $\mathop{\mathrm{KL}}(P^*\|R)$ alone is not
the convergence criterion used here. The finite-state rate is CKMA SYNOPSIS39,
item 90.

Local texts directly consulted or identified for this selection:

- [Ghosal and van der Vaart, *Fundamentals of Nonparametric Bayesian Inference*](../lean-CKMA/ReferencesSuppl/GhosalVanDerVaart2017FundamentalsNonparametricBayesianInference-CambridgeSerStatProbMath44.pdf).
  Theorem 8.9 was read for the contraction criterion.
- [Robert and Casella, *Monte Carlo Statistical Methods*](../lean-CKMA/ReferencesSuppl/RobertCasella2004MonteCarloStatisticalMethods2ndEd-Springer.pdf).
  Chapters 3–4 were consulted for importance sampling and variance reduction.
  Sections 7.8 and 14.3.5 were read.
- [Liu, *Monte Carlo Strategies in Scientific Computing*](../lean-CKMA/ReferencesSuppl/Liu2004MonteCarloStrategiesScientificComputing-SpringerSerStat.pdf).
  Sections 9.2–9.3 were read for hybrid Monte Carlo.
  Section 3.4 (residual resampling) was read.
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
- [Law, Stuart, and Zygalakis, *Data Assimilation: A Mathematical Introduction*](../lean-CKMA/ReferencesSuppl/LawStuartZygalakis2015DataAssimilationMathematicalIntroduction-Springer.TAM62.pdf).
  The two ensemble Kalman variants in Sections 4.2.3–4.2.4 were read.
- [Bishop and Bishop, *Deep Learning: Foundations and Concepts*](../lean-CKMA/References/BishopBishop2024DeepLearningFoundationsConcepts-Springer.pdf).
  Chapter 20 was consulted for diffusion and score models.
- [Chewi, *Log-Concave Sampling*](../lean-CKMA/References/Chewi2026LogConcaveSampling-AuthorManuscript.pdf).
  Theorem 4.3.6 was read; for items 43–50, 59–62, and 73–77 also the passages listed above.
- [Pavliotis, *Stochastic Processes and Applications*](../lean-CKMA/References/Pavliotis2014StochasticProcessesApplications-SpringerTAM.pdf).
- [Kushner and Yin, *Stochastic Approximation and Recursive Algorithms and Applications*](../lean-CKMA/References/KushnerYin2003StochasticApproximationRecursiveAlgorithmsApplications2ndEd-Springer.SMAP35.pdf).
- [Borkar, *Stochastic Approximation: A Dynamical Systems Viewpoint*](../lean-CKMA/References/Borkar2023StochasticApproximationDynamicalSystemsViewpoint2ndEd-SpringerHindustanTRIM48.pdf).
- [Ambrosio, Gigli, and Savaré, *Gradient Flows*](../lean-CKMA/References/AmbrosioGigliSavaré2008GradientFlowsMetricSpacesSpaceProbabilityMeasures2ndEd-Birkhäuser.LMETH.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. I](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications1FBSDEsControl-SpringerPTSM83.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. II](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications2CommonNoiseMasterEquations-SpringerPTSM84.pdf).
- [Figalli and Glaudo, *An Invitation to Optimal Transport, Wasserstein Distances, and Gradient Flows*](../lean-CKMA/References/FigalliGlaudo2021InvitationOptimalTransportWassersteinDistancesGradientFlows-EMS.TextbooksMath.pdf).
  Section 3.3 (JKO scheme) was read.
- [Del Moral, *Feynman–Kac Formulae: Genealogical and Interacting Particle Systems with Applications*](../lean-CKMA/ReferencesSuppl/Moral2004FeynmanKacFormulaeGenealogicalInteractingParticleSystemsApplications-Springer.PIA.pdf).
  Sections 4.4, 7.4, and 9.3–9.4 were read.
- [Peyré and Cuturi, *Computational Optimal Transport*](../lean-CKMA/References/PeyréCuturi2019ComputationalOptimalTransportApplicationsDataSciences-NowPublishers.FnTML11.pdf).
