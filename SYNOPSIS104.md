# Synopsis: Nonparametric, semiparametric, and robust inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-104).

This synopsis follows Section 104. Subdivision 104A is rank methods, smoothing,
shape constraints, and minimax rates. Subdivision 104B is semiparametric
efficiency and missing data. Subdivision 104C is robust estimation.
Subdivision 104D is functional data. Parametric efficiency is
[SYNOPSIS103](SYNOPSIS103.md), items 9–12. The empirical-process limit and the
Dvoretzky–Kiefer–Wolfowitz inequality are
[CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 59, and
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), item 39. High-dimensional
penalties and learning bounds are in Section 107. Nonparametric priors are in
Section 105.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-104a"></a>

## 104A. Ranks, Smoothing, Shape Constraints, and Minimax Estimation

Throughout this subdivision, $X_1,\ldots,X_n$ are independent copies of a real
random variable with distribution function $F$ and, when a density exists,
density $f$. The empirical distribution function is $F_n$.

* **1. Kolmogorov–Smirnov statistic.** If $F$ is continuous, the law of
  $\sup_x|F_n(x)-F(x)|$ does not depend on $F$. By the empirical-process
  limit,
  $$\sqrt n\sup_x|F_n(x)-F(x)|\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,$$
  and for $x>0$
  $$P\bigl(\sup_t|B^0(t)|\le x\bigr)
  =1-2\sum_{k=1}^\infty(-1)^{k-1}e^{-2k^2x^2}.$$
  The Dvoretzky–Kiefer–Wolfowitz inequality supplies the corresponding
  finite-sample tail bound.

* **2. Linear rank statistics.** Let the observations be continuous and
  independent, and let $R_i$ be the rank of the $i$th observation in the
  pooled sample. Under a null hypothesis that makes the vector of ranks
  uniform on the permutations, every rank statistic has a distribution free
  of the unknown continuous law. For scores $a_n(i)$ and regression constants
  $c_{n,i}$ satisfying the usual growth and nondegeneracy conditions, the
  Hájek projection of the linear rank statistic
  $S_n=\sum_i c_{n,i}a_n(R_i)$ is asymptotically normal under the null and
  under contiguous location alternatives. In the two-sample shift problem
  the Wilcoxon rank-sum test is the locally most powerful rank test for the
  logistic shift, and its Pitman efficiency relative to the two-sample $t$
  test, at a normal shift, equals $3/\pi$.

* **3. Hodges–Lehmann estimator.** For a distribution symmetric about
  $\theta$ with density $f$, let $\hat\theta_n$ be the median of the Walsh
  averages $(X_i+X_j)/2$ for $1\le i\le j\le n$. If $\int f^2<\infty$ and
  $f$ is continuous and positive at the center of symmetry of $X_1-X_2$, then
  $$\sqrt n\,(\hat\theta_n-\theta)
  \Rightarrow N\Bigl(0,\frac{1}{12\bigl(\int f(x)^2\,dx\bigr)^2}\Bigr).$$
  The asymptotic variance is the reciprocal of the efficacy of the Wilcoxon
  signed-rank test.

A **kernel density estimator** with bandwidth $h>0$ and kernel $K$ is
$$\hat f_h(x)=\frac1{nh}\sum_{i=1}^n K\bigl((x-X_i)/h\bigr).$$
Write $\mu_2(K)=\int u^2K(u)\,du$ and $R(K)=\int K(u)^2\,du$.

* **4. Kernel density asymptotics.** Let $K$ be a bounded symmetric
  probability density with finite $\mu_2(K)$ and $R(K)$. Let $f$ be twice
  continuously differentiable, with $f$ and $f''$ square-integrable and $f(x)>0$.
  If $h\to0$, $nh\to\infty$, and $nh^5=O(1)$, then
  $$\sqrt{nh}\Bigl(\hat f_h(x)-f(x)-\tfrac12 h^2\mu_2(K)f''(x)\Bigr)
  \Rightarrow N\bigl(0,R(K)f(x)\bigr).$$
  The asymptotic mean integrated squared error is
  $$\tfrac14 h^4\mu_2(K)^2\int(f'')^2+R(K)/(nh),$$
  and the bandwidth of exact order $n^{-1/5}$ minimizes the displayed
  expression. The resulting optimal rate is of order $n^{-4/5}$.

* **5. Universal $L^1$ consistency.** Let $K$ be a bounded integrable kernel
  on $\mathbb R^d$ with $\int K=1$ and compact support. If $h\to0$ and
  $nh^d\to\infty$, then $\int|\hat f_h-f|\to0$ almost surely for every
  density $f$ on $\mathbb R^d$.

For regression, let $(X_i,Y_i)$ be independent copies of $(X,Y)$ with
$m(x)=\mathbb E[Y\mid X=x]$ and $\sigma^2(x)=\mathop{\mathrm{Var}}(Y\mid X=x)$.
The **Nadaraya–Watson** estimator weights $Y_i$ by
$K_h(X_i-x)/\sum_j K_h(X_j-x)$. The **local linear** estimator is the
intercept of the weighted least-squares fit of a straight line, with the same
kernel weights.

* **6. Interior asymptotics of kernel regression.** Let $X$ have density
  $f_X$ continuous and positive at an interior point $x$, let $m$ be twice
  continuously differentiable at $x$, and let $\sigma^2$ be continuous at $x$.
  Assume a locally bounded conditional $(2+\delta)$ moment of $Y$ for
  some $\delta>0$, and a nonnegative bounded symmetric compactly supported
  probability kernel positive near zero. If $h\to0$, $nh\to\infty$, and
  $nh^5=O(1)$, the local linear estimator satisfies
  $$\sqrt{nh}\Bigl(\hat m_h(x)-m(x)-\tfrac12 h^2\mu_2(K)m''(x)\Bigr)
  \Rightarrow N\Bigl(0,\frac{R(K)\sigma^2(x)}{f_X(x)}\Bigr).$$
  If in addition $f_X$ and $m$ are continuously differentiable at $x$, the
  Nadaraya–Watson estimator satisfies the same limit with the bias
  $\tfrac12 h^2\mu_2(K)m''(x)$ replaced by
  $$\tfrac12 h^2\mu_2(K)\Bigl(m''(x)+2m'(x)\frac{f_X'(x)}{f_X(x)}\Bigr).$$
  At a boundary point the local linear bias remains of order $h^2$, while the
  Nadaraya–Watson bias is of order $h$.

* **7. Stone's theorem.** Assume $\mathbb E Y^2<\infty$. For kernel
  regression with a nonnegative bounded compactly supported kernel
  bounded below by a positive constant in a neighborhood of zero,
  $h\to0$ and $nh^d\to\infty$ imply
  $$\mathbb E\bigl[(\hat m_n(X)-m(X))^2\bigm|X_1,Y_1,\ldots,X_n,Y_n\bigr]
  \to0$$
  in probability, for every distribution of $(X,Y)$ on $\mathbb R^d\times\mathbb R$.
  The same universal $L^2$ consistency holds for $k$-nearest-neighbor
  regression when $k\to\infty$ and $k/n\to0$.

Let $\mathcal H$ be a reproducing-kernel Hilbert space of real functions on
a set $\mathcal X$, with kernel $K$. A loss $L(y,u)$ is evaluated only through
the predicted value $u$.

* **8. Representer theorem.** A minimizer of
  $$\frac1n\sum_{i=1}^n L(Y_i,f(X_i))+\lambda\|f\|_{\mathcal H}^2,
  \qquad\lambda>0,$$
  over $f\in\mathcal H$, has the form
  $f(\cdot)=\sum_{i=1}^n\alpha_i K(X_i,\cdot)$. In particular, the smoothing
  spline
  $$\sum_{i=1}^n(Y_i-f(x_i))^2+\lambda\int(f'')^2$$
  on the Sobolev space of square-integrable second derivatives has a
  minimizer that is a natural cubic spline with knots at the design points
  $x_i$.

In the **Gaussian sequence model**, one observes
$Y_i=\theta_i+\varepsilon\xi_i$ for $i\ge1$, with $\xi_i$ independent standard
normal. The white-noise model $dY(t)=f(t)\,dt+\varepsilon\,dW(t)$ on $[0,1]$
is equivalent to a sequence model through an orthonormal basis.

* **9. Pinsker's theorem and the Sobolev rate.** For the ellipsoid
  $\sum_{j\ge1}a_j^2\theta_j^2\le R$ with $a_j$ regularly varying of order
  $\beta>0$, the minimax mean squared error among all estimators is
  asymptotic, as $\varepsilon\to0$, to the minimax risk among linear
  estimators. A linear shrinkage filter attains the asymptotic constant.
  For a Sobolev ball of smoothness $\beta$ and radius $R$ in the white-noise
  model, this risk is of exact order
  $R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)}$. With
  $\varepsilon=n^{-1/2}$ the squared-error rate is
  $n^{-2\beta/(2\beta+1)}$.

* **10. Soft-threshold oracle inequality.** In the finite sequence model
  $Y_i=\theta_i+\sigma\xi_i$, $i=1,\ldots,n$, let $\hat\theta$ be coordinatewise
  soft thresholding at $\lambda=\sigma\sqrt{2\log n}$. Then
  $$\mathbb E\|\hat\theta-\theta\|^2
  \le(2\log n+1)\Bigl(\sigma^2+\sum_{i=1}^n\min(\theta_i^2,\sigma^2)\Bigr).$$
  The estimator therefore tracks, up to the factor $2\log n+1$, the ideal
  risk of an oracle that retains only those coordinates larger than the
  noise level.

* **11. Grenander estimator.** Let $f$ be decreasing and positive on
  $[0,\infty)$, with $f'(x_0)<0$ and $f$ continuous at $x_0>0$. The maximum
  likelihood estimator $\hat f_n$ is the left slope of the least concave
  majorant of $F_n$. Then
  $$n^{1/3}\bigl(\hat f_n(x_0)-f(x_0)\bigr)
  \Rightarrow\bigl|4f(x_0)f'(x_0)\bigr|^{1/3}Z,$$
  where $Z=\mathop{\mathrm{argmax}}_{t\in\mathbb R}\bigl(W(t)-t^2\bigr)$ and
  $W$ is standard two-sided Brownian motion. The limit law is Chernoff's
  distribution up to the deterministic scale displayed above.

Let $K\subset\mathbb R^p$ be a closed polyhedral convex cone and let
$Y\sim N_p(\mu,I_p)$. Write $P_K$ for metric projection onto $K$.

* **12. Chi-bar-squared limit.** The likelihood-ratio statistic for testing
  $\mu=0$ against $\mu\in K$ equals $\|P_KY\|^2$. Under the null its law is
  the mixture $\sum_{j=0}^p w_j\chi^2_j$, where $w_j$ is the probability that
  $P_KY$ lies in the relative interior of a $j$-dimensional face of $K$.
  The same mixture limit, with weights determined by the cone of feasible
  directions after whitening by the information matrix, holds for
  regular fixed-dimensional likelihood-ratio tests with polyhedral tangent
  cones. For Gaussian monotone regression at a fixed finite design,
  the corresponding cone projection gives the finite-sample mixture;
  an increasing-dimensional problem needs its own asymptotic analysis.

Testing $f=0$ in the white-noise model against a smoothness class at a
positive $L^2$ separation is a different problem from estimating $f$.

* **13. Nonparametric detection boundary.** In the white-noise model, the
  minimax separation $\rho_n$ for testing $f=0$ against the alternative
  that $f$ lies in a Sobolev or Hölder ball of smoothness $\beta$ and
  $\|f\|_2\ge\rho_n$ is of order $n^{-2\beta/(4\beta+1)}$. At smaller
  orders no test can separate zero uniformly from all alternatives at that
  separation. At sufficiently larger orders uniformly consistent tests
  exist. The detection separation is smaller than the $L^2$ estimation
  error rate $n^{-\beta/(2\beta+1)}$ of item 9.

### Exact ranks, smoothing bias, and shape constraints

* **22. Sign test.** For independent continuous observations with median
  $\theta_0$, $\sum_i1_{\{X_i>\theta_0\}}\sim\mathop{\mathrm{Bin}}(n,1/2)$.
  Binomial tails give exact or conservative tests of the median without a
  symmetry assumption. Inversion is the quantile interval in SYNOPSIS101,
  item 18. Symmetry is needed for the signed-rank procedure below.

* **23. Wilcoxon sampling laws.** Under a continuous distribution symmetric
  about zero, the signs are independent fair signs and independent of the
  absolute values. Thus the positive signed-rank sum has the law
  $\sum_{j=1}^n jB_j$ for independent Bernoulli$(1/2)$ variables, with
  mean $n(n+1)/4$ and variance $n(n+1)(2n+1)/24$.
  For independent samples of sizes $m,n$ from a common continuous law,
  $U=\sum_{i,j}1_{\{X_i<Y_j\}}$ has mean $mn/2$ and variance
  $mn(m+n+1)/12$. Both centered, variance-normalized statistics tend to
  $N(0,1)$, in the second case when $m/(m+n)\to\lambda\in(0,1)$.

* **24. Kruskal–Wallis test.** For $k$ independent samples from a common
  continuous law, let $R_j$ be the sum of pooled ranks in group $j$, of
  size $n_j$, and put $N=\sum_jn_j$. For fixed $k$ and
  $n_j/N\to\lambda_j>0$,
  $$\frac{12}{N(N+1)}\sum_{j=1}^k\frac{R_j^2}{n_j}-3(N+1)
  \Rightarrow\chi^2_{k-1}.$$
  Its finite-sample permutation law is distribution-free. The statistic
  tests equality of distributions; a location interpretation requires a
  common-shape shift model.

* **25. Isotonic least squares.** For observations $y_i$ at ordered design
  points and weights $w_i>0$, the minimizer of
  $\sum_iw_i(y_i-\theta_i)^2$ over $\theta_1\le\cdots\le\theta_n$ is unique
  and satisfies
  $$\hat\theta_i=\max_{a\le i}\min_{b\ge i}
  \frac{\sum_{j=a}^bw_jy_j}{\sum_{j=a}^bw_j}.$$
  It is the vector of successive slopes of the greatest convex minorant
  of the cumulative-sum diagram
  $(\sum_{j\le i}w_j,\sum_{j\le i}w_jy_j)$, including $(0,0)$.
  Pooling adjacent blocks whose weighted means violate monotonicity
  computes this projection.

* **26. Hölder regression rates.** In Gaussian regression on $[0,1]^d$
  with fixed positive noise variance and a design density bounded above and
  below by positive constants, the minimax integrated squared error over
  a fixed Hölder ball of smoothness $\beta>0$ is of order
  $n^{-2\beta/(2\beta+d)}$. Boundary-adapted local polynomials of degree
  at least $\lceil\beta\rceil-1$, with bandwidth of order
  $n^{-1/(2\beta+d)}$, attain this order. Under the same regular design
  conditions the minimax expected squared supremum error is of order
  $(\log n/n)^{2\beta/(2\beta+d)}$. The testing reductions in SYNOPSIS107,
  items 14 and 15, supply matching lower bounds.

Bias matters for confidence statements even at a mean-squared-error optimal
bandwidth. For the second-order smoothers of items 4 and 6, $nh^5\to0$
makes the leading $h^2$ bias negligible relative to $(nh)^{-1/2}$.
At $h\asymp n^{-1/5}$ it has the same order as the standard error, so
pointwise intervals require bias correction or undersmoothing.

<a id="synopsis-104b"></a>

## 104B. Semiparametric Models and Missing Data

A **semiparametric model** is a family $\{P_{\theta,\eta}\}$ in which $\theta$
is a Euclidean parameter and the nuisance parameter $\eta$ ranges over an
infinite-dimensional set. A parametric submodel $t\mapsto P_{\theta,\eta_t}$
that varies only the nuisance parameter has a nuisance score. The
**nuisance tangent space** is the closed linear span of the nuisance scores
of smooth finite-dimensional submodels. The **efficient score** $\tilde\ell_\theta$
is the residual of the ordinary score for $\theta$ after orthogonal projection
onto that tangent space, and the **efficient information** is
$\tilde I(\theta)=\mathbb E[\tilde\ell_\theta\tilde\ell_\theta^\top]$.

* **14. Semiparametric convolution bound.** Assume local asymptotic normality
  of every regular finite-dimensional submodel, nonsingular efficient
  information, and the usual differentiability of the parameter along those
  submodels. Every regular estimator sequence of $\theta$ has a limit law
  equal to the convolution of $N(0,\tilde I(\theta)^{-1})$ with some
  probability measure on the parameter space. An estimator is asymptotically
  linear with influence function equal to $\tilde I(\theta)^{-1}\tilde\ell_\theta$
  if and only if it attains this bound. The ordinary parametric bound of
  SYNOPSIS103, item 11, is the case of a finite-dimensional nuisance
  parameter.

Let $Y$ be a response, let $X$ be covariates that are always observed, and
let $R$ indicate whether $Y$ is observed. The observations are independent
copies of $(R,X,RY)$. The response is **missing at random** when
$P(R=1\mid X,Y)=P(R=1\mid X)$. It is **missing completely at random** when
$R$ is independent of $(X,Y)$. Write $\pi(x)=P(R=1\mid X=x)$ and
$m(x)=\mathbb E[Y\mid R=1,X=x]$.

* **15. Ignorability.** Under missingness at random, the density of the
  observed data factors into a part that depends on the law of $(X,Y)$ and a
  part that depends on the missingness mechanism. If those two parameters
  are variation-independent, the maximizer of the observed-data likelihood
  for the law of $(X,Y)$ does not depend on the missingness parameter. The
  mechanism is then ignorable for likelihood inference.

For a complete-data density $f(x\mid\theta)$ and observed data $Y=t(X)$, the
**EM iteration** from $\theta'$ maximizes
$Q(\theta\mid\theta')=\mathbb E_{\theta'}[\log f(X\mid\theta)\mid Y]$ and
sets the next value equal to that maximizer.

* **16. Monotonicity of EM.** The observed-data log-likelihood at the new
  value is at least the observed-data log-likelihood at $\theta'$. A fixed
  point of a continuous EM map at which $Q$ has a unique maximizer is a
  stationary point of the observed-data likelihood.

* **17. Double robustness for a missing mean.** Under missingness at random
  and $\pi_0(X)\ge\delta>0$, the estimating function
  $$\varphi_{m,\pi}(R,X,Y)
  =\frac{RY}{\pi(X)}-\frac{R-\pi(X)}{\pi(X)}m(X)$$
  has expectation $\mathbb E Y$ as soon as either $\pi=\pi_0$, with $m$ any
  square-integrable function, or $m(x)=\mathbb E[Y\mid X=x]$, with $\pi$ any
  measurable function bounded away from zero. The estimator obtained by
  substituting estimators of $m$ and $\pi$ and taking the sample average is
  therefore consistent when at least one of the two fitted models is
  correct. If both are correct and converge quickly enough, the estimator
  is asymptotically linear with the efficient influence function for
  $\mathbb E Y$.

### Pathwise derivatives and orthogonal estimation

For a scalar parameter $\psi(P)$, let $\mathcal T\subset L^2_0(P)$ be the
closed tangent space of scores of differentiable submodels. The parameter
is **pathwise differentiable** if its derivative along every score $s$ is
$\dot\psi_P(s)=P(\phi s)$ for some $\phi\in L^2_0(P)$. The unique such
representative in $\mathcal T$ is the **canonical gradient**.

* **27. Canonical gradient and efficiency.** If a regular asymptotically
  linear estimator has influence function $\phi$, its projection onto
  $\mathcal T$ is the canonical gradient $\phi_{\mathrm{eff}}$. Hence
  $$P\phi^2=P\phi_{\mathrm{eff}}^2
  +P(\phi-\phi_{\mathrm{eff}})^2.$$
  The efficient variance bound is $P\phi_{\mathrm{eff}}^2$. In the
  unrestricted model, the mean has canonical gradient $x-PX$, and the
  $p$-quantile with positive density has gradient
  $(p-1_{\{x\le q_p\}})/f(q_p)$. A derivative that has no continuous
  $L^2$ representation precludes regular estimation at rate $\sqrt n$.

* **28. Cross-fitted estimation of a missing mean.** Use a fixed finite
  number of folds, evaluating the estimating function in item 17 on each
  fold with nuisance estimates trained on the other folds. Suppose
  $Y\in L^2$, the true and fitted response probabilities are bounded below
  by $\delta>0$, both nuisance estimates are $L^2$ consistent, and
  $$\|\hat m-m_0\|_2\,\|\hat\pi-\pi_0\|_2=o_P(n^{-1/2}).$$
  If the fitted estimating functions also converge in $L^2$ to the true
  one, then
  $$\sqrt n(\hat\mu-\mu)
  =n^{-1/2}\sum_{i=1}^n
  \left[m_0(X_i)+\frac{R_i(Y_i-m_0(X_i))}{\pi_0(X_i)}-\mu\right]+o_P(1).$$
  The variance is the efficient bound of item 27. Conditional second-moment
  bounds on $Y$ and bounded or suitably truncated regressions are useful
  sufficient conditions for the additional $L^2$ convergence. Sample
  splitting avoids requiring a Donsker class for the fitted nuisances.

* **29. Partially linear regression.** Suppose
  $Y=D^\top\beta+g(X)+\varepsilon$, $\mathbb E[\varepsilon\mid D,X]=0$,
  and $\mathbb E[\varepsilon^2\mid D,X]=\sigma^2\in(0,\infty)$. Write
  $V=D-\mathbb E[D\mid X]$ and assume $Q=\mathbb E[VV^\top]$ is positive
  definite. Then
  $$\beta=Q^{-1}\mathbb E[V(Y-\mathbb E[Y\mid X])].$$
  In the model imposing the conditional mean restriction, with conditional
  variance unrestricted away from the true law, the efficient influence
  function at this homoscedastic law is $Q^{-1}V\varepsilon$, with
  covariance $\sigma^2Q^{-1}$. Residualizing both $Y$ and $D$
  and fitting least squares attains this bound under consistent nuisance
  estimation and appropriate product-rate and moment conditions, using
  cross-fitting as in item 28.

<a id="synopsis-104c"></a>

## 104C. Robust Statistics

For a functional $T$ defined on a neighborhood of a distribution $F$, the
**influence function** at $x$ is
$$\mathop{\mathrm{IF}}(x;T,F)
=\lim_{\varepsilon\downarrow0}
\frac{T((1-\varepsilon)F+\varepsilon\delta_x)-T(F)}{\varepsilon},$$
when the limit exists. The **gross-error sensitivity** is the supremum of
$|\mathop{\mathrm{IF}}(x;T,F)|$ over $x$. The finite-sample **breakdown
point** of an estimator at a sample is the smallest fraction of the sample
that can be replaced so that the estimator becomes arbitrarily large or
otherwise leaves every compact set of the parameter space.

* **18. M-estimators and the Huber minimax property.** An $M$-functional of
  location defined by $\int\psi(x-\theta)\,dF(x)=0$, with $\psi$ odd and
  $\int\psi'\,dF\neq0$, has influence function
  $\psi(x-\theta)/\int\psi'\,dF$. For a location sample its estimator is
  asymptotically normal with variance
  $\mathbb E\psi(X-\theta)^2/(\mathbb E\psi'(X-\theta))^2$, under the
  standard Lipschitz and nondegeneracy conditions of SYNOPSIS103, item 4.
  Among Fisher-consistent location functionals whose gross-error sensitivity
  at the standard normal law is at most a prescribed bound, the asymptotic
  variance at that law is minimized by Huber's clipped score
  $\psi_k(u)=\max(-k,\min(k,u))$ for a clip $k$ determined by the bound.
  The same score is minimax for asymptotic variance over
  $\varepsilon$-contamination neighborhoods of the normal law.

* **19. Breakdown points.** The sample mean has replacement breakdown
  point $1/n$ at a sample of size $n$, tending to zero as $n\to\infty$. The
  sample median of a one-dimensional sample of size $n=2m+1$ has breakdown
  point $(m+1)/n$, which tends to $1/2$. Ordinary least squares has
  breakdown point $1/n$. The least-median-of-squares regression estimator
  has breakdown point that tends to $1/2$ as $n\to\infty$ with the number of
  covariates fixed.

* **30. Influence of a median and a contamination bound.** If $F$ has
  unique median $m$ and a positive continuous density there, the median
  functional has influence function
  $$\frac{1/2-1_{\{x\le m\}}}{f(m)},\qquad x\ne m.$$
  Its asymptotic variance is $1/(4f(m)^2)$ and its gross-error sensitivity
  is $1/(2f(m))$. For $G=(1-\varepsilon)F+\varepsilon H$,
  $0\le\varepsilon<1/2$, with continuous strictly increasing $F$, every
  median of $G$ lies between
  $$F^{-1}\left(\frac{1/2-\varepsilon}{1-\varepsilon}\right)
  \quad\hbox{and}\quad
  F^{-1}\left(\frac{1/2}{1-\varepsilon}\right).$$
  Extreme contaminating distributions approach these bounds. Bounded
  local influence and a positive breakdown point describe different
  aspects of robustness.

<a id="synopsis-104d"></a>

## 104D. Functional Data Analysis

Let $X$ be a random element of a separable Hilbert space $H$ with
$\mathbb E\|X\|^2<\infty$, mean $\mu$, and covariance operator
$C=\mathbb E[(X-\mu)\otimes(X-\mu)]$. Then $C$ is compact, self-adjoint,
nonnegative, and trace-class. Its eigenvalues and orthonormal eigenfunctions
are $(\lambda_j,\varphi_j)$.

* **20. Karhunen–Loève expansion and the Hilbertian central limit theorem.**
  For each positive eigenvalue, set
  $\xi_j=\langle X-\mu,\varphi_j\rangle/\sqrt{\lambda_j}$.
  These variables are uncorrelated with mean $0$ and variance $1$, and
  $$X=\mu+\sum_{j\ge1}\sqrt{\lambda_j}\,\xi_j\varphi_j,$$
  where only positive eigenvalues are included, with convergence in $L^2$
  and almost surely in $H$. For independent copies,
  $\sqrt n\,(\bar X_n-\mu)$ converges in law in $H$ to the centered Gaussian
  random element with covariance operator $C$.

* **21. Principal components of the empirical covariance.** Let $\hat C_n$ be
  the empirical covariance and let $\hat\lambda_j$ and $\hat\varphi_j$ be its
  eigenvalues and eigenfunctions. If $\lambda_j$ is simple and positive and
  $\mathbb E\|X\|^4<\infty$, then
  $$\sqrt n\,(\hat\lambda_j-\lambda_j)
  \Rightarrow N\bigl(0,\mathop{\mathrm{Var}}(\langle X-\mu,\varphi_j\rangle^2)\bigr).$$
  For a Gaussian $X$ the asymptotic variance equals $2\lambda_j^2$. The
  empirical eigenfunction, multiplied by a sign so that
  $\langle\hat\varphi_j,\varphi_j\rangle\ge0$, satisfies
  $\|\hat\varphi_j-\varphi_j\|=O_P(n^{-1/2}/\delta_j)$, where
  $\delta_j$ is the distance from $\lambda_j$ to the rest of the spectrum.
  Its first-order expansion is
  $$\hat\varphi_j-\varphi_j
  =\sum_{k\ne j}\frac{\langle(\hat C_n-C)\varphi_j,\varphi_k\rangle}
  {\lambda_j-\lambda_k}\varphi_k+o_P(n^{-1/2}),$$
  with the zero eigenspace included when present.

* **31. Optimality of functional principal components.** If the eigenvalues
  of $C$ are ordered decreasingly, then among all orthogonal projections
  $P_V$ onto $k$-dimensional subspaces of $H$,
  $$\inf_{\dim V=k}\mathbb E\|X-\mu-P_V(X-\mu)\|^2
  =\sum_{j>k}\lambda_j.$$
  The first $k$ eigenfunctions span a minimizing subspace. If
  $\lambda_k>\lambda_{k+1}$, that subspace is unique. This reconstruction
  characterization does not require Gaussian observations.

## Reference guide

### Correspondence with the subdivisions

- **[104A](#synopsis-104a)**: Wand and Jones, Fan and Gijbels, Wahba,
  Groeneboom and Jongbloed, Johnstone's Gaussian-sequence draft, the
  wavelet monograph of Härdle, Kerkyacharian, Picard, and Tsybakov, and
  Ingster and Suslina carry the smoothing expansions, the representer
  theorem, shape-constrained limits, and the sequence-model minimax theory.
  Rank asymptotics are the subject of Hájek, Šidák, and Sen.
- **[104B](#synopsis-104b)**: Bickel, Klaassen, Ritov, and Wellner, Kosorok,
  Little and Rubin, and van der Laan and Robins carry efficiency bounds,
  ignorability, EM, and double robustness.
- **[104C](#synopsis-104c)**: Jurečková and Sen develop the asymptotics of
  $M$-estimators. Huber and Ronchetti, and Hampel, Ronchetti, Rousseeuw,
  and Stahel, are the organizing monographs for influence functions and
  breakdown.
- **[104D](#synopsis-104d)**: Hsing and Eubank develop the Hilbert-space
  geometry, the covariance operator, and the asymptotics of functional
  principal components.

### Source comparisons and local copies

Hollander, Wolfe, and Chicken, Chapters 3, 4, and 6, provide the exact
sign and rank procedures and the several-sample comparison added here.
Robertson, Wright, and Dykstra, Section 1.2 and the max–min formulas of
Section 1.4, give the cumulative-sum and pooling descriptions of isotonic
regression. Wand–Jones and Fan–Gijbels supply the bias expansions; the
bandwidth conditions now ensure that replacing the exact bias by its
leading term is legitimate in the normal limit. Tsybakov's full text is
available in `ReferencesSuppl`; its regression upper and lower bound
chapters were consulted, including the supremum-norm comparison in
Corollary 2.5. Item 26 records the corresponding dimension-dependent
Hölder rates. Hsing–Eubank, Chapters 1 and 9, supplies the reconstruction
interpretation and the spectral perturbation framework.

Items 27–29 make the semiparametric geometry operational: representing
derivatives in $L^2$, projecting out nuisance regressions, and controlling
the product remainder after sample splitting. They give explicit
conditions for the efficiency claims in items 14 and 17, rather than
treating consistency of fitted nuisances alone as sufficient for a
central limit theorem.

The kernel expansions of items 4 and 6 are the interior-point formulae of
Wand and Jones and of Fan and Gijbels. Item 8 is the Kimeldorf–Wahba
representer theorem, as used throughout Wahba's spline monograph. Items 9
and 10 follow Johnstone's chapters on Pinsker's theorem and on thresholding.
Item 11 is the pointwise limit in Groeneboom and Jongbloed. Item 13 is the
Sobolev detection boundary of Ingster and Suslina. Item 12 is the cone
mixture of Robertson, Wright, and Dykstra.

Lehmann's *Nonparametrics*, Silverman's density monograph, and the
Györfi, Kohler, Krzyżak, and Walk distribution-free regression monograph
were not located in the local reference directories. Hájek, Šidák, and Sen is present as a DjVu file
and was not text-extracted. Huber and Ronchetti, and Hampel, Ronchetti,
Rousseeuw, and Stahel, are also absent locally; items 18 and 19 are the
forms used by Jurečková and Sen and by the robust chapters of the general
inference texts. Tsiatis's missing-data monograph is absent locally; item 17
is the augmented inverse-probability function of that book and of van der
Laan and Robins.

Local texts directly consulted for this selection:

- [Hollander, Wolfe, and Chicken, *Nonparametric Statistical Methods*](../lean-CKMA/References/HollanderWolfeChicken2014NonparametricStatisticalMethods3rdEd-Wiley.SerProbStat.pdf).
- [Tsybakov, *Introduction to Nonparametric Estimation*](../lean-CKMA/ReferencesSuppl/Tsybakov2009IntroductionNonparametricEstimation-SpringerSSS.pdf).
- [Wand and Jones, *Kernel Smoothing*](../lean-CKMA/References/WandJones1995KernelSmoothing-ChapmanHallCRC.MSAP60.pdf).
- [Fan and Gijbels, *Local Polynomial Modelling and Its Applications*](../lean-CKMA/References/FanGijbels1996LocalPolynomialModellingApplications-ChapmanHallCRC.MSAP66.pdf).
- [Wahba, *Spline Models for Observational Data*](../lean-CKMA/References/Wahba1990SplineModelsObservationalData-SIAM.CBMS59.pdf).
- [Groeneboom and Jongbloed, *Nonparametric Estimation under Shape Constraints*](../lean-CKMA/References/GroeneboomJongbloed2014NonparametricEstimationShapeConstraintsEstimatorsAlgorithmsAsymptotics-Cambridge.SerStatProbMath.pdf).
- [Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*](../lean-CKMA/References/Johnstone2017GaussianEstimationSequenceWaveletModels-AuthorManuscript.pdf).
- [Härdle, Kerkyacharian, Picard, and Tsybakov, *Wavelets, Approximation, and Statistical Applications*](../lean-CKMA/References/HärdleKerkyacharianPicardTsybakov1998WaveletsApproximationStatisticalApplications-Springer.LNS129.pdf).
- [Ingster and Suslina, *Nonparametric Goodness-of-Fit Testing Under Gaussian Models*](../lean-CKMA/References/IngsterSuslina2003NonparametricGoodnessFitTestingGaussianModels-Springer.LNS169.pdf).
- [Robertson, Wright, and Dykstra, *Order Restricted Statistical Inference*](../lean-CKMA/References/RobertsonWrightDykstra1988OrderRestrictedStatisticalInference-Wiley.SerProbStat.pdf).
- [Devroye and Lugosi, *Combinatorial Methods in Density Estimation*](../lean-CKMA/References/DevroyeLugosi2001CombinatorialMethodsDensityEstimation-Springer.SSS.pdf).
- [Bickel, Klaassen, Ritov, and Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*](../lean-CKMA/References/BickelKlaassenRitovWellner1993EfficientAdaptiveEstimationSemiparametricModels-JohnsHopkins.MathSci.pdf).
- [Kosorok, *Introduction to Empirical Processes and Semiparametric Inference*](../lean-CKMA/References/Kosorok2008IntroductionEmpiricalProcessesSemiparametricInference-Springer.SSS.pdf).
- [Little and Rubin, *Statistical Analysis with Missing Data*](../lean-CKMA/References/LittleRubin2020StatisticalAnalysisMissingData3rdEd-Wiley.SerProbStat.pdf).
- [van der Laan and Robins, *Unified Methods for Censored Longitudinal Data and Causality*](../lean-CKMA/References/VanDerLaanRobins2003UnifiedMethodsCensoredLongitudinalDataCausality-Springer.SSS.pdf).
- [Jurečková and Sen, *Robust Statistical Procedures*](../lean-CKMA/References/JurečkováSen1996RobustStatisticalProceduresAsymptoticsInterrelations-Wiley.SerProbStat.pdf).
- [Hsing and Eubank, *Theoretical Foundations of Functional Data Analysis*](../lean-CKMA/References/HsingEubank2015TheoreticalFoundationsFunctionalDataAnalysisIntroductionLinearOperators-Wiley.SerProbStat.pdf).
- [Hájek, Šidák, and Sen, *Theory of Rank Tests*](../lean-CKMA/References/HájekŠidákSen1999TheoryRankTests2ndEd-AcademicPress.djvu).
