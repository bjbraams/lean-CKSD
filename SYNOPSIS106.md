# Synopsis: Linear models, multivariate analysis, and experimental design

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-106).

This synopsis follows Section 106. Subdivision 106A is the linear model,
the analysis of variance and variance components, generalised linear
models, quantiles, and finite mixtures. Subdivision 106B
is classical multivariate analysis, graphical models, and directional data.
Subdivision 106C is experimental design, including block, factorial,
and Latin-square designs. Simultaneous confidence procedures
for the linear model are [SYNOPSIS102](SYNOPSIS102.md), items 16 and 17.
Likelihood-ratio asymptotics are [SYNOPSIS103](SYNOPSIS103.md), item 7.
High-dimensional covariance and sparsity are in Section 107.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-106a"></a>

## 106A. Regression, Generalised Linear Models, and Mixtures

Throughout this subdivision, $Y$ is an $n$-vector of responses, $X$ is a fixed
$n\times p$ design matrix, and the mean of $Y$ is $X\beta$ unless a statement
says otherwise. Write $r=\mathop{\mathrm{rank}}(X)$.

* **1. Gauss–Markov theorem.** Assume $\mathbb E\varepsilon=0$ and
  $\mathop{\mathrm{Cov}}(\varepsilon)=\sigma^2 I_n$. Among linear unbiased
  estimators of an estimable functional $c^\top\beta$, the least-squares
  estimator has the smallest variance. If $X$ has full column rank, the
  covariance $\sigma^2(X^\top X)^{-1}$ of the least-squares estimator is the
  Loewner minimum of the covariances of linear unbiased estimators of $\beta$.
  The comparison uses the first two moments of $\varepsilon$.

Let $P$ be the orthogonal projection onto the column space of $X$, and write
$\mu=\mathbb EY$.

* **2. Normal sampling theory.** If $\varepsilon\sim N(0,\sigma^2 I_n)$, then
  $\|PY\|^2/\sigma^2$ has the noncentral chi-squared law on $r$ degrees of
  freedom with noncentrality $\|P\mu\|^2/\sigma^2$, and $\|PY\|^2$ is
  independent of $\|(I-P)Y\|^2$. The residual sum of squares
  $\|(I-P)Y\|^2/\sigma^2$ is chi-squared on $n-r$ degrees of freedom. When
  $X$ has full column rank, the least-squares estimator is normal with mean
  $\beta$ and covariance $\sigma^2(X^\top X)^{-1}$, and it is independent of
  the residual sum of squares.

An **exponential dispersion family** has density
$$\exp\Bigl(\frac{y\theta-b(\theta)}{a(\varphi)}+c(y,\varphi)\Bigr)$$
with respect to a dominating measure. Then $\mathbb EY=b'(\theta)$ and
$\mathop{\mathrm{Var}}(Y)=b''(\theta)\,a(\varphi)$. A **generalised linear
model** specifies $g(\mu_i)=x_i^\top\beta$ for a link $g$, with
$\eta_i=x_i^\top\beta$. The link is canonical when the natural parameter
equals $\eta_i$. Write $V$ for the variance function in the case
$a(\varphi)=\varphi$, so that $\mathop{\mathrm{Var}}(Y_i)=\varphi V(\mu_i)$,
and write $W=\mathop{\mathrm{diag}}\bigl((d\mu_i/d\eta_i)^2/V(\mu_i)\bigr)$.

* **3. Asymptotics of the generalised linear model.** For independent
  responses from an exponential dispersion family, with $a(\varphi)=\varphi$
  and with the design and link satisfying the usual full-rank and interior
  conditions, the Fisher information for $\beta$ is $\varphi^{-1}X^\top WX$.
  The maximum likelihood estimator is asymptotically normal with covariance
  equal to the inverse of this information, and a consistent estimator of
  $\varphi$ may be substituted. The difference of the deviances of two nested
  regular models is the likelihood-ratio statistic of SYNOPSIS103, item 7,
  and is asymptotically chi-squared on the difference of the dimensions under
  the smaller model.

* **4. Quasi-likelihood.** Let $D_i=\partial\mu_i/\partial\beta$ and let $V_i$
  be a positive definite working covariance. A root $\hat\beta$ of the
  estimating equation $\sum_i D_i^\top V_i^{-1}(Y_i-\mu_i(\beta))=0$ is
  asymptotically normal whenever the mean $\mu(\beta)$ is correctly specified
  and the usual regularity conditions hold. A consistent estimator of its
  covariance is the sandwich
  $$A_n^{-1}B_nA_n^{-1},$$
  where $A_n=\sum_i D_i^\top V_i^{-1}D_i$ and
  $B_n=\sum_i D_i^\top V_i^{-1}\widehat{\mathop{\mathrm{Cov}}}(Y_i)\,V_i^{-1}D_i$.
  If $V_i$ equals the true covariance, the sandwich reduces to $A_n^{-1}$.

The **check function** of order $\tau\in(0,1)$ is
$\rho_\tau(u)=u(\tau-1_{\{u<0\}})$. The $\tau$-quantile regression estimator
minimizes $\sum_{i=1}^n\rho_\tau(Y_i-x_i^\top\beta)$.

* **5. Quantile regression.** Let $\beta_\tau$ be a minimizer of the
  population criterion $\mathbb E\rho_\tau(Y-x^\top\beta)$ in an
  independent random-design sample, and assume the conditional
  $\tau$-quantile is correctly specified as $x^\top\beta_\tau$.
  Write $\varepsilon=Y-x^\top\beta_\tau$. Suppose that the conditional density of
  $\varepsilon$ given $x$ is continuous and positive at $0$, that
  $D_0=\mathbb E[xx^\top]$ and
  $D_1=\mathbb E[f_{\varepsilon\mid x}(0)\,xx^\top]$ are finite, and that
  $D_1$ is nonsingular. Then
  $$\sqrt n\,(\hat\beta_\tau-\beta_\tau)
  \Rightarrow N\bigl(0,\,\tau(1-\tau)\,D_1^{-1}D_0D_1^{-1}\bigr).$$

* **6. Finite normal mixtures.** A finite mixture of nondegenerate Gaussian
  distributions on $\mathbb R^d$, with distinct component parameters
  and strictly positive weights, is identifiable up to permutation of
  the component labels. With at least two components and unconstrained
  component covariance matrices, the likelihood is unbounded: a
  component mean placed at an observation, with that component's variance sent
  to zero, drives the likelihood to infinity. The EM iteration of SYNOPSIS104,
  item 16, can diverge to this boundary.

* **7. Residual maximum likelihood.** In the Gaussian linear model of item 2,
  the maximum likelihood estimator of $\sigma^2$ is the residual sum of
  squares divided by $n$. The residual maximum likelihood estimator, formed
  from the likelihood of any full-rank set of error contrasts, is the residual
  sum of squares divided by $n-r$. That estimator is unbiased for $\sigma^2$.

### Linear-model reductions and diagnostics

A linear functional $c^\top\beta$ is **estimable** when an unbiased
linear estimator $a^\top Y$ exists. In the model with mean $X\beta$, this
is equivalent to $c\in\mathop{\mathrm{col}}(X^\top)$. Fitted values and
estimable functionals are unique even if a least-squares coefficient vector
is not. The following formulas involving $(X^\top X)^{-1}$ assume full
column rank.

* **18. Generalized least squares.** If the error covariance is
  $\sigma^2V$, with $V$ known positive definite, then
  $$\hat\beta_V=(X^\top V^{-1}X)^{-1}X^\top V^{-1}Y,\qquad
  \mathop{\mathrm{Cov}}(\hat\beta_V)
  =\sigma^2(X^\top V^{-1}X)^{-1}.$$
  It is the best linear unbiased estimator. Multiplication by $V^{-1/2}$
  reduces the problem to item 1. With Gaussian errors the corresponding
  normal, chi-squared, and $F$ laws hold after this transformation.

* **19. Partial regression.** Partition $X=(X_1,X_2)$ and let
  $M_1=I-P_{X_1}$. If $X$ has full column rank, the coefficient of $X_2$
  in the full least-squares fit is
  $$(X_2^\top M_1X_2)^{-1}X_2^\top M_1Y.$$
  Thus projecting both the response and the regressors off the nuisance
  columns yields the same coefficient and residual sum of squares. This
  is the Frisch–Waugh–Lovell theorem; its conditional-mean analogue is
  SYNOPSIS104, item 29.

* **20. Exact tests of nested linear models.** Let $P_0,P_1$ project onto
  nested model spaces of dimensions $r_0<r_1<n$. Under the smaller model
  and independent $N(0,\sigma^2)$ errors,
  $$\frac{\|(P_1-P_0)Y\|^2/(r_1-r_0)}
  {\|(I-P_1)Y\|^2/(n-r_1)}\sim F_{r_1-r_0,n-r_1}.$$
  The numerator and denominator sums of squares, divided by $\sigma^2$,
  are independent chi-squared variables. Under the larger model the
  numerator has noncentrality
  $\|(P_1-P_0)X\beta\|^2/\sigma^2$. A single estimable contrast gives
  the square of the usual Student $t$ statistic.

* **21. Leverage, deletion, and prediction error.** Write
  $H=X(X^\top X)^{-1}X^\top$, $h_i=H_{ii}$, and $e=(I-H)Y$.
  Then $0\le h_i\le1$, $\sum_i h_i=p$, and
  $\mathop{\mathrm{Cov}}(e)=\sigma^2(I-H)$. If $h_i<1$, deleting case
  $i$ preserves the design rank and gives
  $$\hat\beta_{(-i)}=\hat\beta-
  \frac{(X^\top X)^{-1}x_i e_i}{1-h_i},\qquad
  Y_i-x_i^\top\hat\beta_{(-i)}=\frac{e_i}{1-h_i}.$$
  Hence the leave-one-out squared prediction criterion is
  $n^{-1}\sum_i(e_i/(1-h_i))^2$ without refitting $n$ models. Under
  normal errors, the externally studentized residual
  $e_i/(s_{(-i)}\sqrt{1-h_i})$ has law $t_{n-p-1}$ when $n>p+1$.

* **22. Ridge bias and variance.** For $\lambda>0$, the minimizer of
  $\|Y-Xb\|^2+\lambda\|b\|^2$ is
  $\hat\beta_\lambda=(X^\top X+\lambda I)^{-1}X^\top Y$, even for a
  rank-deficient design. If $\mathbb E\varepsilon=0$ and
  $\mathop{\mathrm{Cov}}\varepsilon=\sigma^2I$, its bias is
  $-\lambda(X^\top X+\lambda I)^{-1}\beta$ and its covariance is
  $$\sigma^2(X^\top X+\lambda I)^{-1}X^\top X
  (X^\top X+\lambda I)^{-1}.$$
  The fitted-value map has effective degrees of freedom
  $\mathop{\mathrm{tr}}[X(X^\top X+\lambda I)^{-1}X^\top]$.

* **23. Canonical likelihood and separation.** For a canonical generalized
  linear model with known dispersion, the log-likelihood in $\beta$ is
  concave, with negative Hessian $\varphi^{-1}X^\top W X$.
  It is strictly concave when $X$ has full column rank and all variance
  weights are positive; thus any finite score root is the unique maximum.
  In binary logistic regression, if a nonzero $b$ satisfies
  $(2Y_i-1)x_i^\top b\ge0$ for every $i$, with strict inequality for at
  least one observation, the likelihood increases along that direction
  and has no finite maximizer. Strict inequalities for every $i$ give
  complete separation. Concavity does not by itself establish existence.

* **24. Prediction in a linear mixed model.** Suppose
  $Y=X\beta+Zu+\varepsilon$, where $u$ and $\varepsilon$ are centered,
  uncorrelated, with known covariance matrices $G$ and $R>0$, and
  $X$ has full column rank. Set $V=ZGZ^\top+R$ and let $\hat\beta_V$ be generalized least squares.
  The best linear unbiased predictor of $u$ is
  $$\hat u=GZ^\top V^{-1}(Y-X\hat\beta_V).$$
  Here unbiasedness is averaged over both random components and holds
  for every $\beta$. If $\beta$ is known and the components are jointly
  Gaussian, $GZ^\top V^{-1}(Y-X\beta)=\mathbb E[u\mid Y]$; with unknown
  fixed effects, substitution of $\hat\beta_V$ gives the stated predictor.

### Quadratic forms and the analysis of variance

For a $k$-vector $Z\sim N_k(m,I_k)$, the law of $\|Z\|^2$ is the
**noncentral chi-squared law** on $k$ degrees of freedom with
noncentrality $\|m\|^2$; this is the convention of item 2.

* **29. Distribution of quadratic forms.** Let $Y\sim N_n(\mu,\Sigma)$
  with $\Sigma$ positive definite, and let $A$ and $B$ be symmetric.
  If $A\Sigma$ is idempotent of rank $r$, then $Y^\top AY$ is noncentral
  chi-squared on $r$ degrees of freedom with noncentrality
  $\mu^\top A\mu$; for $\mu=0$, $Y^\top AY$ is chi-squared on $r$ degrees
  of freedom only if $A\Sigma$ is idempotent of rank $r$. If
  $A\Sigma B=0$, then $Y^\top AY$ and $Y^\top BY$ are independent; for
  $\mu=0$ the condition is also necessary (Craig–Sakamoto). In the case
  $\Sigma=I_n$, Cochran's theorem states: if
  $Y^\top Y=\sum_{i=1}^kY^\top A_iY$ with $\mathop{\mathrm{rank}}A_i=n_i$,
  then the forms $Y^\top A_iY$ are independent noncentral chi-squared
  variables, on $n_i$ degrees of freedom with noncentralities
  $\mu^\top A_i\mu$, if and only if $\sum_in_i=n$.

* **30. Optimality of the $F$ test.** In the setting of item 20, the
  power of the $F$ test of fixed level depends on the parameters only
  through the noncentrality
  $\delta^2=\|(P_1-P_0)X\beta\|^2/\sigma^2$, and it is strictly increasing
  in $\delta^2$. Among level-$\alpha$ tests invariant under the group
  generated by positive rescaling of $Y$, translation within the smaller
  model space, and orthogonal transformations of the residual space and
  of the hypothesis space $\mathop{\mathrm{col}}(P_1-P_0)$, the $F$ test
  is uniformly most powerful. Among all similar tests of level $\alpha$, it
  maximizes the average power over every sphere of alternatives with
  fixed $\delta^2$, fixed nuisance mean component, and fixed $\sigma$.

* **31. Balanced two-way layout.** Let $Y_{ijk}=\eta_{ij}+e_{ijk}$ for
  $i\le I$, $j\le J$, $k\le K$, with $K\ge2$ and independent
  $N(0,\sigma^2)$ errors. Define the general mean, main effects, and
  interactions by $\mu=\eta_{\cdot\cdot}$,
  $\alpha_i=\eta_{i\cdot}-\eta_{\cdot\cdot}$,
  $\beta_j=\eta_{\cdot j}-\eta_{\cdot\cdot}$, and
  $\gamma_{ij}=\eta_{ij}-\eta_{i\cdot}-\eta_{\cdot j}+\eta_{\cdot\cdot}$,
  dots denoting unweighted averages. Their least-squares estimators
  replace each $\eta$ by the corresponding cell mean of the data. The
  total sum of squares splits orthogonally as
  $$\sum_{ijk}Y_{ijk}^2=IJK\bar Y_{\cdot\cdot\cdot}^2
  +\mathrm{SS}_A+\mathrm{SS}_B+\mathrm{SS}_{AB}+\mathrm{SS}_e,$$
  with $1$, $I-1$, $J-1$, $(I-1)(J-1)$, and $IJ(K-1)$ degrees of freedom,
  where for instance
  $\mathrm{SS}_A=JK\sum_i(\bar Y_{i\cdot\cdot}-\bar Y_{\cdot\cdot\cdot})^2$
  and $\mathrm{SS}_e=\sum_{ijk}(Y_{ijk}-\bar Y_{ij\cdot})^2$. These five
  quadratic forms are independent; divided by $\sigma^2$, the last is
  central chi-squared and the others are noncentral chi-squared, with
  noncentralities $JK\sum_i\alpha_i^2/\sigma^2$,
  $IK\sum_j\beta_j^2/\sigma^2$, and $K\sum_{ij}\gamma_{ij}^2/\sigma^2$ for
  the two main-effect and the interaction terms. The hypotheses of no
  main effect and of no interaction are tested by the corresponding $F$
  ratios against $\mathrm{SS}_e/(IJ(K-1))$. If some cell is empty, the main
  effects and interactions defined above are not estimable.

Consider the balanced one-way random model
$Y_{ij}=\mu+a_i+e_{ij}$, $i\le a$, $j\le n$, $a\ge2$, $n\ge2$, with all
$a_i$ and $e_{ij}$ independent, $a_i\sim N(0,\sigma_a^2)$ and
$e_{ij}\sim N(0,\sigma_e^2)$. Write
$\mathrm{MSA}=n\sum_i(\bar Y_{i\cdot}-\bar Y_{\cdot\cdot})^2/(a-1)$ and
$\mathrm{MSE}=\sum_{ij}(Y_{ij}-\bar Y_{i\cdot})^2/(a(n-1))$.

* **32. One-way variance components.** Here
  $(a-1)\mathrm{MSA}/(n\sigma_a^2+\sigma_e^2)$ and
  $a(n-1)\mathrm{MSE}/\sigma_e^2$ are independent chi-squared variables on
  $a-1$ and $a(n-1)$ degrees of freedom. Hence
  $\mathbb E\,\mathrm{MSA}=n\sigma_a^2+\sigma_e^2$ and
  $\mathbb E\,\mathrm{MSE}=\sigma_e^2$, and the analysis-of-variance
  estimators $\hat\sigma_e^2=\mathrm{MSE}$ and
  $\hat\sigma_a^2=(\mathrm{MSA}-\mathrm{MSE})/n$ are unbiased; the first
  two moment equalities need only uncorrelated components with these
  variances. The estimator $\hat\sigma_a^2$ is negative with probability
  $$P\bigl(F_{a(n-1),\,a-1}>1+n\sigma_a^2/\sigma_e^2\bigr)>0.$$
  When $\mathrm{MSA}\ge\mathrm{MSE}$ these estimators are the residual
  maximum likelihood estimators of item 7. The maximum likelihood
  estimator of $\sigma_a^2$, when positive, is
  $((1-1/a)\mathrm{MSA}-\mathrm{MSE})/n$.

* **33. Mallows' $C_p$.** In the model $Y=\mu+\varepsilon$ with
  $\mathbb E\varepsilon=0$ and $\mathop{\mathrm{Cov}}\varepsilon=\sigma^2I_n$,
  let a candidate submodel have an $n\times p$ design $X_p$ of full rank,
  projection $P_p$, and residual sum of squares $\mathrm{RSS}_p$. The
  model error $\mathrm{ME}_p=\|P_pY-\mu\|^2$ satisfies
  $$\mathbb E\,\mathrm{RSS}_p=\|(I-P_p)\mu\|^2+(n-p)\sigma^2
  =\mathbb E\,\mathrm{ME}_p+(n-2p)\sigma^2.$$
  Thus $\mathrm{RSS}_p+(2p-n)\sigma^2$ is unbiased for
  $\mathbb E\,\mathrm{ME}_p$, and
  $C_p=\mathrm{RSS}_p/\hat\sigma^2+2p-n$, with an independent or
  full-model estimator $\hat\sigma^2$, estimates
  $\mathbb E\,\mathrm{ME}_p/\sigma^2$. For a submodel whose column
  space contains $\mu$, $\mathbb E\,\mathrm{RSS}_p/\sigma^2+2p-n=p$.
  Selection over many submodels by minimizing $C_p$ is governed by
  SYNOPSIS107, items 3 and 4.

### Fitting and assessing generalised linear models

* **34. Fisher scoring as iteratively reweighted least squares.** In
  the generalised linear model with $a(\varphi)=\varphi$, let $\beta^{(t)}$
  be the current value, with linear predictor $\eta^{(t)}=X\beta^{(t)}$,
  mean $\mu^{(t)}$, and weights $W^{(t)}$ as in item 3. Form the adjusted
  response
  $$z_i=\eta_i^{(t)}+(Y_i-\mu_i^{(t)})\,g'(\mu_i^{(t)}).$$
  One step of Fisher scoring for the likelihood equations is the
  weighted least-squares fit
  $$\beta^{(t+1)}=(X^\top W^{(t)}X)^{-1}X^\top W^{(t)}z.$$
  The dispersion $\varphi$ cancels from the update. For a canonical
  link, the expected and observed information agree, so this is
  Newton's method, and under item 23 a limit is the unique maximizer.

For a generalised linear model with $a_i(\varphi)=\varphi/w_i$, the
**deviance** of fitted means $\hat\mu$ is
$D(y;\hat\mu)=\varphi\cdot2\{\ell(y;y)-\ell(\hat\mu;y)\}$, where
$\ell(y;y)$ is the log-likelihood of the saturated model that fits each
observation exactly; $D/\varphi$ is the **scaled deviance**.

* **35. Deviance.** The deviance does not depend on $\varphi$. Summing
  over observations with unit prior weights, it equals $\sum(y-\hat\mu)^2$ for the normal model,
  $$2\sum\bigl\{y\log(y/\hat\mu)-(y-\hat\mu)\bigr\}$$
  for the Poisson model, and
  $$2\sum\bigl\{y\log(y/\hat\mu)+(m-y)\log((m-y)/(m-\hat\mu))\bigr\}$$
  for binomial counts out of $m$, with $0\log0=0$. Maximizing the
  likelihood minimizes the deviance, and for nested models fitted by
  maximum likelihood the deviances are additive, giving the analysis of
  deviance. Differences of scaled deviances obey item 3. The residual
  scaled deviance itself is close to chi-squared on $n-p$ degrees of
  freedom only in a small-dispersion regime, such as large binomial
  indices or large Poisson means; for binary data it is a function of
  $\hat\beta$ alone and carries no information on fit.

<a id="synopsis-106b"></a>

## 106B. Multivariate Analysis, Invariance, and Graphical Models

* **8. Wishart distribution and Hotelling's $T^2$.** Let $Z_1,\ldots,Z_n$ be
  independent $N_p(0,\Sigma)$ with $n\ge p$ and with $\Sigma$ positive
  definite. Then $W=\sum_{i=1}^n Z_iZ_i^\top$ has the Wishart distribution
  $W_p(n,\Sigma)$. For an independent normal sample of size $n\ge p+1$, the
  sample mean $\bar X$ and the sample covariance $S$ with divisor $n-1$ are
  independent, and $(n-1)S\sim W_p(n-1,\Sigma)$. Hotelling's statistic
  $T^2=n(\bar X-\mu)^\top S^{-1}(\bar X-\mu)$ satisfies
  $$\frac{n-p}{(n-1)p}\,T^2\sim F_{p,\,n-p}$$
  when the true mean is $\mu$.

* **9. Wilks's lambda.** In a multivariate normal linear model, let $E$ and
  $H$ be the residual and hypothesis sums of squares and products, and let
  $\Lambda=\det(E)/\det(E+H)$. Under the null hypothesis, $\Lambda$ has the
  same law as a product of independent beta random variables, with parameters
  determined by the response dimension $p$, the hypothesis degrees of freedom
  $h$, and the error degrees of freedom $e$. Bartlett's statistic
  $$-\bigl(e-(p-h+1)/2\bigr)\log\Lambda$$
  is asymptotically chi-squared on $ph$ degrees of freedom as $e\to\infty$,
  and the displayed multiplier is the standard finite-sample correction to
  $-e\log\Lambda$.

* **10. Principal component eigenvalues.** Let $S_n$ be the sample covariance,
  with divisor $n$, of an independent normal sample in $\mathbb R^p$, and let
  $\lambda_j$ be a simple positive eigenvalue of the population covariance.
  The corresponding eigenvalue $\hat\lambda_j$ of $S_n$ satisfies
  $$\sqrt n\,(\hat\lambda_j-\lambda_j)\Rightarrow N(0,2\lambda_j^2).$$

* **11. Fisher's linear discriminant.** Consider two classes with priors
  $\pi_1>0$ and $\pi_2>0$, Gaussian conditional laws with means $\mu_1$
  and $\mu_2$, and a common positive definite covariance $\Sigma$. The Bayes rule for $0$–$1$ loss assigns an
  observation $x$ to class $1$ when
  $$(\mu_1-\mu_2)^\top\Sigma^{-1}\Bigl(x-\frac{\mu_1+\mu_2}2\Bigr)
  >\log\frac{\pi_2}{\pi_1}.$$
  The decision boundary is affine. If the two class covariances differ, the
  Bayes boundary is quadratic.

Let $G$ be an undirected graph with vertex set $\{1,\ldots,p\}$. A positive
continuous density on $\mathbb R^p$ satisfies the **pairwise Markov property**
when $X_i$ and $X_j$ are conditionally independent given the remaining
coordinates whenever $\{i,j\}$ is not an edge. It satisfies the **global
Markov property** when separation in $G$ implies the corresponding conditional
independence.

* **12. Undirected graphical models.** For a positive continuous density, the
  pairwise Markov property, the local Markov property, and the global Markov
  property are equivalent. Under the same positivity condition, the
  Hammersley–Clifford theorem gives a factorization of the density into a
  product of positive functions, each depending on the coordinates in a single
  clique. For a nondegenerate Gaussian law, $X_i$ and $X_j$ are conditionally
  independent given the remaining coordinates if and only if the $(i,j)$ entry
  of the precision matrix vanishes.

The **von Mises–Fisher** density on the unit sphere $S^{p-1}$ is
$c_p(\kappa)\exp(\kappa\mu\cdot x)$, with $\|\mu\|=1$ and concentration
$\kappa\ge0$.

* **13. von Mises–Fisher model.** The maximum likelihood estimator of the mean
  direction $\mu$ is the direction of the resultant $\sum_{i=1}^n X_i$. On the
  circle, $\mathbb E[\cos(X-\mu)]=I_1(\kappa)/I_0(\kappa)$, and the likelihood
  equation for $\kappa$ equates this function to the mean resultant length.

### Covariance geometry and multivariate reduction

* **25. Gaussian covariance likelihood.** For a normal sample with unknown
  mean and positive definite covariance, if the centered sample spans
  $\mathbb R^p$, the maximum likelihood estimators are
  $$\hat\mu=\bar X,\qquad
  \hat\Sigma=\frac1n\sum_i(X_i-\bar X)(X_i-\bar X)^\top.$$
  If that scatter matrix is singular, the likelihood is unbounded over
  positive definite covariance matrices and there is no finite covariance
  maximizer in that space. This occurs almost surely when $n\le p$.
  Dividing by $n-1$ instead gives the unbiased covariance estimator whose
  Wishart law is item 8.

* **26. Canonical correlations.** For centered random vectors $(U,V)$
  with positive definite marginal covariances, the largest correlation
  between $a^\top U$ and $b^\top V$ is the largest singular value of
  $$\Sigma_{UU}^{-1/2}\Sigma_{UV}\Sigma_{VV}^{-1/2}.$$
  Subsequent singular values solve the same maximization with successive
  variates uncorrelated within each vector. They lie in $[0,1]$ and are
  unchanged by nonsingular linear transformations within $U$ or $V$.
  For a jointly Gaussian pair, all canonical correlations vanish if and
  only if $U$ and $V$ are independent.

* **27. Principal components and reconstruction.** For a centered vector
  with covariance eigenvalues $\lambda_1\ge\cdots\ge\lambda_p\ge0$,
  the first $k$ eigenvectors maximize captured variance
  $\mathop{\mathrm{tr}}(P\Sigma)$ among rank-$k$ orthogonal projections.
  The minimal mean squared reconstruction error is
  $\sum_{j>k}\lambda_j$. For a centered data matrix, truncating its singular
  value decomposition gives the best rank-$k$ approximation in Frobenius
  norm. Functional observations are covered by SYNOPSIS104, item 31;
  fixed-dimensional eigenvalue asymptotics are item 10.

### Wishart structure and correlation coefficients

* **36. Structure of the Wishart law.** Let $W\sim W_p(n,\Sigma)$ with
  $n\ge p$ an integer and $\Sigma$ positive definite. Then $W$ has density
  $$\frac{(\det w)^{(n-p-1)/2}\exp\bigl(-\tfrac12\mathop{\mathrm{tr}}(\Sigma^{-1}w)\bigr)}
  {2^{np/2}(\det\Sigma)^{n/2}\,\Gamma_p(n/2)}$$
  on positive definite matrices, where $\Gamma_p$ is the multivariate
  gamma function. For a $k\times p$ matrix $M$ of rank $k$,
  $MWM^\top\sim W_k(n,M\Sigma M^\top)$. Partition $W$ and $\Sigma$ into
  blocks of sizes $k$ and $p-k$. Then $W_{22}\sim W_{p-k}(n,\Sigma_{22})$,
  and the Schur complement $W_{11\cdot2}=W_{11}-W_{12}W_{22}^{-1}W_{21}$ is
  $W_k(n-p+k,\Sigma_{11\cdot2})$ and independent of $(W_{12},W_{22})$.
  If $\Sigma=I_p$ and $W=T^\top T$ with $T$ upper triangular with
  positive diagonal, the entries $t_{ij}$, $i\le j$, are independent, with
  $t_{ii}^2\sim\chi^2_{n-i+1}$ and $t_{ij}\sim N(0,1)$ for $i<j$; this is the
  Bartlett decomposition. Consequently $\det W/\det\Sigma$ has the law of
  a product of independent $\chi^2_{n-i+1}$ variables,
  $i=1,\ldots,p$.

* **37. Sampling theory of correlation coefficients.** Let $r$ be the
  sample correlation of $N$ independent observations from a bivariate
  normal law with correlation $\rho$. If $\rho=0$ and $N>2$, then
  $\sqrt{N-2}\,r/\sqrt{1-r^2}$ has law $t_{N-2}$. As $N\to\infty$,
  $$\sqrt N\,(r-\rho)\Rightarrow N\bigl(0,(1-\rho^2)^2\bigr),\qquad
  \sqrt N\,(\mathop{\mathrm{artanh}}r-\mathop{\mathrm{artanh}}\rho)
  \Rightarrow N(0,1),$$
  the second being Fisher's variance-stabilizing $z$ transformation. For
  a $p$-variate normal sample, the sample partial correlation of two
  coordinates given $p-q$ other coordinates has the law of an ordinary
  sample correlation from $N-(p-q)$ observations with $\rho$ replaced by
  the population partial correlation. If the population multiple
  correlation of $X_1$ with $(X_2,\ldots,X_p)$ vanishes and $N>p$, the
  sample multiple correlation $R$ satisfies
  $$\frac{R^2}{1-R^2}\cdot\frac{N-p}{p-1}\sim F_{p-1,\,N-p}.$$

### Tests on covariance structure and multivariate hypotheses

In the next item, $X_1,\ldots,X_N$ are independent $N_p(\mu,\Sigma)$ with
$N>p$, $n=N-1$, and $A=\sum_i(X_i-\bar X)(X_i-\bar X)^\top$.

* **38. Likelihood-ratio tests of sphericity and independence.** For
  $H:\Sigma=\lambda I_p$ with $\lambda>0$ unspecified, the likelihood
  ratio is $V^{N/2}$ with
  $$V=\frac{\det A}{\bigl(\mathop{\mathrm{tr}}A/p\bigr)^p}.$$
  Under $H$, $-N\log V\Rightarrow\chi^2_f$ with $f=p(p+1)/2-1$, and with
  $$\rho=1-\frac{2p^2+p+2}{6pn}$$
  the distribution function of $-n\rho\log V$ differs from that of
  $\chi^2_f$ by $O(n^{-2})$. For independence of $k$ subvectors of sizes
  $p_1,\ldots,p_k$, the likelihood ratio is $\Lambda^{N/2}$ with
  $\Lambda=\det A/\prod_i\det A_{ii}$, and under independence
  $-N\log\Lambda\Rightarrow\chi^2_f$ with
  $f=\sum_{i<j}p_ip_j$; Box's multiplier again reduces the error to
  $O(N^{-2})$. For $k=2$,
  $\Lambda=\prod_i(1-r_i^2)$, where the $r_i$ are the sample canonical
  correlations of item 26.

* **39. Invariant tests of a multivariate linear hypothesis.** In the
  setting of item 9 let $E$ be positive definite, and let
  $l_1\ge\cdots\ge l_p\ge0$ be the roots of $\det(H-lE)=0$. Under the
  group of nonsingular linear maps of the response, together with the
  translations and orthogonal maps that leave the problem invariant,
  these roots form a maximal invariant, so every invariant test is a
  function of them. Wilks's statistic is $\prod_i(1+l_i)^{-1}$, the
  Lawley–Hotelling trace is $\mathop{\mathrm{tr}}HE^{-1}=\sum_il_i$,
  the Pillai trace is $\mathop{\mathrm{tr}}H(H+E)^{-1}=\sum_il_i/(1+l_i)$,
  and Roy's statistic is $l_1$. Under the null hypothesis,
  $e\mathop{\mathrm{tr}}HE^{-1}\Rightarrow\chi^2_{ph}$ as $e\to\infty$.
  If $\min(p,h)=1$ there is at most one nonzero root, and all four tests
  reduce to the same exact $F$ test, as for Hotelling's $T^2$ in item 8.

The **orthogonal factor model** with $m$ factors states
$X=\mu+\Lambda f+u$, where $\Lambda$ is a $p\times m$ loading matrix,
$f$ has mean $0$ and covariance $I_m$, $u$ is uncorrelated with $f$ and
has mean $0$ and diagonal positive definite covariance $\Psi$. Then
$\mathop{\mathrm{Cov}}X=\Lambda\Lambda^\top+\Psi$.

* **40. Factor analysis and identification.** For every orthogonal
  $m\times m$ matrix $O$, the loadings $\Lambda O$ give the same
  covariance, so $\Lambda$ can be identified only after
  $m(m-1)/2$ further conditions. One standard choice requires
  $\Lambda^\top\Psi^{-1}\Lambda$ to be diagonal with distinct diagonal
  entries in decreasing order; given $\Lambda\Lambda^\top$, this fixes
  $\Lambda$ up to the signs of its columns. Whether $\Sigma$ determines
  $\Lambda\Lambda^\top$ and $\Psi$ is a separate question, and the count
  $$\tfrac12\bigl[(p-m)^2-p-m\bigr]$$
  of covariance entries plus identifying conditions minus free parameters
  is the degrees of freedom of the asymptotic chi-squared law of the
  Gaussian likelihood-ratio test of the $m$-factor model, under the
  regularity conditions for asymptotic normality of the estimators. Under
  this identification, if the sample covariance converges in probability
  to $\Lambda\Lambda^\top+\Psi$, the Gaussian maximum likelihood
  estimators are consistent.

### Decomposable graphical models

An undirected graph is **decomposable** when every cycle of length at least
four has a chord. Its cliques can then be ordered so that each meets the
union of the earlier ones in a complete **separator**, and the multiset of
separators, with multiplicities $\nu(S)$, does not depend on the chosen
perfect order. For a matrix $B$ indexed by a subset $C$ of the vertices,
$[B]^V$ denotes the $p\times p$ matrix with $B$ in the block $C\times C$
and zeros elsewhere.

* **41. Decomposable models.** For a decomposable graph with cliques
  $\mathcal C$ and separators $\mathcal S$, a positive density is globally
  Markov if and only if
  $$f(x)=\frac{\prod_{C\in\mathcal C}f_C(x_C)}
  {\prod_{S\in\mathcal S}f_S(x_S)^{\nu(S)}},$$
  with $f_C,f_S$ the marginal densities. In the Gaussian model whose
  concentration matrix vanishes off the edges, let $\mathrm{ssd}$ be the
  centered sum-of-squares matrix of $n$ observations. The maximum
  likelihood estimator exists with probability one if and only if
  $n>\max_C|C|$, and then
  $$\hat K=n\Bigl(\sum_{C\in\mathcal C}\bigl[(\mathrm{ssd}_C)^{-1}\bigr]^V
  -\sum_{S\in\mathcal S}\nu(S)\bigl[(\mathrm{ssd}_S)^{-1}\bigr]^V\Bigr).$$
  For a general graph, the estimate, when it exists, is the unique
  positive definite $\hat\Sigma$ that matches $\mathrm{ssd}/n$ on the
  diagonal and on the edges and whose inverse vanishes off the edges. It
  exists whenever $\mathrm{ssd}$ is positive definite, in particular almost
  surely when $n>p$, and iterative proportional scaling converges to it.

<a id="synopsis-106c"></a>

## 106C. Experimental Design

For a regression with regressor $f(x)\in\mathbb R^p$ and a design given by a
probability measure $\xi$, the information matrix is
$M(\xi)=\int f(x)f(x)^\top\,\xi(dx)$.

* **14. Kiefer–Wolfowitz equivalence.** Assume $M(\xi^*)$ is nonsingular. The
  design $\xi^*$ maximizes $\det M(\xi)$ if and only if
  $$\max_x f(x)^\top M(\xi^*)^{-1}f(x)=p,$$
  with equality for every $x$ in the support of $\xi^*$. For a design
  criterion that is concave and strictly increasing with respect to the
  Loewner order on information matrices, a design is optimal if and only if
  the directional derivative of the criterion at $M(\xi^*)$ is nonpositive in
  the direction of every one-point design.

* **15. Randomization test.** Under the sharp null hypothesis that each unit's
  response is unchanged by its treatment assignment, redraw the assignment
  from the randomization distribution while holding the responses fixed. The
  induced distribution of a test statistic is free of unknown parameters.
  The test that rejects when the observed statistic lies in the upper fraction
  $\alpha$ of this distribution has conditional level at most $\alpha$ given
  the responses, and therefore unconditional level at most $\alpha$. When the
  randomization distribution is atomless, or when ties are broken by an
  auxiliary randomization, the conditional level equals $\alpha$.

For a block design with $v$ treatments, let $N$ be the treatment-by-block
incidence matrix, let $R$ be the diagonal matrix of treatment replications,
and let $K$ be the diagonal matrix of block sizes. The **information matrix**
of the treatment effects in the additive block model is
$C=R-NK^{-1}N^\top$.

* **16. Connectedness and estimability.** The design is connected if and only
  if $\mathop{\mathrm{rank}}(C)=v-1$. A treatment contrast $c^\top\tau$ is
  estimable if and only if $c$ lies in the column space of $C$.

An $N\times k$ array on $s$ symbols is an **orthogonal array of strength $t$**
when, in every set of $t$ columns, every possible $t$-tuple appears equally
often.

* **17. Orthogonal arrays.** Use orthogonal contrasts for each factor.
  In an array of strength $t$, distinct effect columns of orders $r,s$
  are orthogonal when $r+s\le t$. In particular, a factorial model
  containing effects through order $q$ has mutually orthogonal columns
  when $2q\le t$; under independent homoscedastic errors its least-squares
  contrast estimators are uncorrelated. Effects of order less than $t$
  need not all be mutually orthogonal, since their products can involve
  more than $t$ factors.

* **28. Balanced incomplete blocks.** In a balanced incomplete block design
  with $v$ treatments, common replication $r$, block size $k$, and pair
  concurrence $\lambda>0$, one has $r(k-1)=\lambda(v-1)$ and
  $$C=\frac{\lambda v}{k}\left(I-\frac1v11^\top\right).$$
  Consequently every treatment contrast is estimable in the additive
  homoscedastic block model and has best linear unbiased variance
  $\sigma^2 k\|c\|^2/(\lambda v)$ for $1^\top c=0$.

### Optimality of block and polynomial designs

For a connected block design $d$ let $\mu_1,\ldots,\mu_{v-1}$ be the
positive eigenvalues of its information matrix $C_d$. The design is
**A-optimal** in a class if it minimizes $\sum_i\mu_i^{-1}$, which is
proportional to the average variance of the estimated pairwise treatment
differences; **D-optimal** if it maximizes $\prod_i\mu_i$; and
**E-optimal** if it maximizes $\min_i\mu_i$. A disconnected design is worst
under each criterion.

* **42. Fisher's inequality and optimality of balanced incomplete
  blocks.** A balanced incomplete block design with $v$ treatments and
  $b$ blocks satisfies $b\ge v$. Every block design with $b$ blocks of
  size $k<v$ has $\mathop{\mathrm{tr}}C_d\le b(k-1)$, with equality exactly
  when no treatment occurs twice in a block. A balanced incomplete block
  design attains this bound and, by item 28, has all $v-1$ positive
  eigenvalues equal to $\lambda v/k=b(k-1)/(v-1)$. Hence, if one exists,
  it is A-, D-, and E-optimal among all block designs with the same
  $v$, $b$, and $k$. More generally it minimizes every criterion of $C_d$
  that is convex, invariant under relabeling of treatments, and
  nonincreasing under multiplication of $C_d$ by scalars at least $1$;
  this is Kiefer's universal optimality.

* **43. D-optimal polynomial regression.** For polynomial regression of
  degree $d\ge1$ on $[-1,1]$, with $f(t)=(1,t,\ldots,t^d)^\top$, the
  unique design maximizing $\det M(\xi)$ assigns weight $1/(d+1)$ to each of
  the $d+1$ roots of $(1-t^2)P_d'(t)$, where $P_d$ is the Legendre
  polynomial of degree $d$. By item 14,
  $\max_tf(t)^\top M(\xi)^{-1}f(t)=d+1$ for this design, the maximum being
  attained exactly at its support points.

### Latin squares and regular fractions

A **Latin square** of order $n$ is an $n\times n$ array of $n$ symbols in
which each symbol occurs once in every row and once in every column. Two
Latin squares of order $n$ are **orthogonal** when, superimposed, every
ordered pair of symbols occurs in exactly one cell.

* **44. Latin squares and mutually orthogonal sets.** In the additive
  model with row, column, and treatment effects for a Latin square of order
  $n\ge3$, with independent homoscedastic errors, the spaces of row,
  column, and treatment contrasts are mutually orthogonal. The
  analysis of variance splits the corrected total sum of squares into
  rows, columns, treatments, and residual, with $n-1$, $n-1$, $n-1$, and
  $(n-1)(n-2)$ degrees of freedom. The least-squares estimator of a
  difference of two treatment effects is the difference of the two
  treatment means, with variance $2\sigma^2/n$. A set of $k$ mutually
  orthogonal Latin squares of order $s$ is equivalent to an orthogonal
  array with $s^2$ rows, $k+2$ columns on $s$ symbols, and strength $2$.
  Consequently $k\le s-1$, and the bound is attained when $s$ is a prime
  power.

In a $2^m$ factorial, write each factorial effect as a word in the factor
letters. A **regular $2^{m-l}$ fraction** is the set of treatment
combinations on which every word of a chosen subgroup of $2^l$ words,
the **defining contrast subgroup**, has a fixed sign. Two effects are
**aliased** when their product lies in that subgroup. The **resolution**
of the fraction is the length of the shortest nonidentity defining word.

* **45. Aliasing and resolution.** In a regular $2^{m-l}$ fraction, each
  effect not in the defining subgroup is aliased with exactly $2^l-1$
  others, and aliased effects have identical contrast columns up to sign,
  so only their signed sum is estimable. An effect of order $r$ and a
  distinct effect of order $s$ can be aliased only if $r+s\ge R$, where
  $R$ is the resolution. In resolution III no two main effects are
  aliased; in resolution IV no main effect is aliased with a two-factor
  interaction; in resolution V no two-factor interaction is aliased with
  another. A regular fraction of resolution $R$ is an orthogonal array of
  strength $R-1$, as in item 17, and $R-1$ is its maximal strength.

## Reference guide

### Correspondence with the subdivisions

- **[106A](#synopsis-106a)**: Rao, Scheffé, Seber and Lee, and Christensen
  carry the linear model, quadratic forms, and the analysis of variance. McCullagh and Nelder carry generalised linear
  models and quasi-likelihood. Koenker carries quantile regression.
  McLachlan and Peel carry finite mixtures. Searle, Casella, and McCulloch
  carry residual maximum likelihood in the linear model.
- **[106B](#synopsis-106b)**: Anderson, Muirhead, Mardia, Kent, and Bibby,
  Eaton, and Bilodeau and Brenner carry the Wishart, Hotelling, Wilks, and
  principal-component limits and discriminant analysis. Lauritzen carries
  graphical models. Mardia and Jupp carry the von Mises–Fisher likelihood.
  Anderson and Muirhead also carry correlation theory, covariance tests,
  and factor analysis.
- **[106C](#synopsis-106c)**: Silvey, Pukelsheim, and Fedorov and Hackl carry
  optimal design. Cox and Reid, Bailey, and Cheng carry randomization and
  block designs. Hedayat, Sloane, and Stufken carry orthogonal arrays.
  Cheng carries Latin squares, regular fractions, and resolution.

### Source comparisons and local copies

For the expansion, Seber–Lee's Section 3.10 was read for generalized
least squares and Section 10.1 for case deletion and studentization;
its Chapters 4 and 12 supply the nested-model and shrinkage framework.
Anderson's Chapters 3, 11, and 12 cover normal covariance likelihood,
principal components, and canonical correlations. The partial-regression,
ridge, and balanced-block formulas are given with their matrix and rank
conditions. Item 17 now imposes the sum-of-orders condition on effect
columns; strength $t$ alone does not decorrelate all effects of orders
less than $t$.

For the third expansion, the following passages were read. Rao's
Section 3b.4 and its Complement 1.5 (Fisher–Cochran and Craig–Sakamoto),
Seber–Lee's Theorems 2.7–2.9 and corollary, and Searle, Casella, and
McCulloch's display (59) and (62) give item 29. Scheffé's Section 2.10,
Theorems 1–3, gives item 30, and his Section 4.3, Tables 4.3.2–4.3.3,
gives item 31. Searle, Casella, and McCulloch's Section 3.5, displays
(60)–(63) and (74), with the comparison of ML, REML, and ANOVA
estimators at (146), gives item 32. Seber–Lee's Section 12.3.2, (12.17)–(12.19),
gives item 33. McCullagh and Nelder's Sections 2.3 and 2.5, and Davison's
Section 10.3.2 on chi-squared approximations for deviances, give items 34
and 35. Muirhead's Theorems 3.2.1, 3.2.5, 3.2.10, 3.2.14, and 3.2.15
give item 36; his Theorems 5.1.1, 5.1.6, and 5.1.7, with Anderson's
Theorems 4.3.5 and 4.4.2, give item 37; his Theorems 8.3.2, 8.3.7,
11.2.1, and 11.2.5 give item 38. Anderson's Section 8.6, Theorem 8.6.1
and Corollary 8.6.1, gives item 39, and his Sections 14.2–14.3, with
Theorem 14.3.1 and the test of the number of factors, give item 40.
Lauritzen's Proposition 3.19, Theorem 5.3, Theorem 5.4, and
Proposition 5.9 give item 41. Bailey's Theorem 11.2, Cheng's Exercise
2.5, and Pukelsheim's Section 14.9 give item 42; the trace bound and the
eigenvalue comparison are elementary. Pukelsheim's Section 9.5 gives
item 43. Cheng's Section 8.6 with Theorem 8.10, Bailey's Section 9.2, Cox
and Reid's Section 5.6 on fractional replication, and Cheng's Theorem 9.5
give items 44 and 45.

The local Agresti copies of *Foundations of Linear and Generalized Linear
Models* and *Categorical Data Analysis* are image scans without usable
text extraction in this pass. They were not used as full-text evidence;
the linear-model expansion uses Seber–Lee and Anderson, and the canonical
likelihood calculation specializes the exponential-family formulas in
SYNOPSIS101.

Item 5 is the asymptotic covariance in Koenker. Item 8 uses the sample
covariance with divisor $n-1$, so that $(n-1)S$ is Wishart on $n-1$ degrees
of freedom. Item 10 uses the divisor $n$; the two normalizations differ by
$o_P(n^{-1/2})$ for a fixed eigenvalue. Item 14 is the equivalence theorem
for $D$-optimality, together with the general equivalence theorem for concave
Loewner-isotone criteria.

Shape analysis in the sense of Kendall and of Dryden and Mardia is recorded
in [SYNOPSIS110](SYNOPSIS110.md), item 6. Diaconis and Wijsman develop the
group-invariance theory behind the sampling laws of this section; the
numbered entries record the sampling consequences.

Local texts directly consulted or identified for this selection:

- [Rao, *Linear Statistical Inference and Its Applications*](../lean-CKMA/References/Rao1973LinearStatisticalInferenceApplications2ndEd-WileySerProbStat.pdf).
- [Scheffé, *The Analysis of Variance*](../lean-CKMA/References/Scheffé1959AnalysisVariance-Wiley.pdf).
- [Seber and Lee, *Linear Regression Analysis*](../lean-CKMA/References/SeberLee2003LinearRegressionAnalysis2ndEd-WileySerProbStat.pdf).
- [Christensen, *Plane Answers to Complex Questions*](../lean-CKMA/References/Christensen2020PlaneAnswersComplexQuestionsTheoryLinearModels5thEd-SpringerSTS.pdf).
- [Searle, Casella, and McCulloch, *Variance Components*](../lean-CKMA/References/SearleCasellaMcCulloch2006VarianceComponents-Wiley.pdf).
- [McCullagh and Nelder, *Generalized Linear Models*](../lean-CKMA/References/McCullaghNelder1989GeneralizedLinearModels2ndEd-ChapmanHallCRC.MSAP37.pdf).
- [Hastie and Tibshirani, *Generalized Additive Models*](../lean-CKMA/References/HastieTibshirani1990GeneralizedAdditiveModels-ChapmanHallCRC.MSAP43.pdf).
- [Agresti, *Foundations of Linear and Generalized Linear Models*](../lean-CKMA/References/Agresti2015FoundationsLinearGeneralizedLinearModels-Wiley.SerProbStat.pdf).
- [Koenker, *Quantile Regression*](../lean-CKMA/References/Koenker2005QuantileRegression-Cambridge.EconometricSocMonographs38.pdf).
- [McLachlan and Peel, *Finite Mixture Models*](../lean-CKMA/References/McLachlanPeel2000FiniteMixtureModels-Wiley.SerProbStat.pdf).
- [Anderson, *An Introduction to Multivariate Statistical Analysis*](../lean-CKMA/References/Anderson2003IntroductionMultivariateStatisticalAnalysis3rdEd-WileySerProbStat.pdf).
- [Muirhead, *Aspects of Multivariate Statistical Theory*](../lean-CKMA/References/Muirhead2005AspectsMultivariateStatisticalTheory-Wiley.pdf).
- [Mardia, Kent, and Bibby, *Multivariate Analysis*](../lean-CKMA/References/MardiaKentBibby1979MultivariateAnalysis-AcademicPress.pdf).
- [Eaton, *Multivariate Statistics*](../lean-CKMA/References/Eaton2007MultivariateStatisticsVectorSpaceApproach-IMS.LNMS53.pdf).
- [Davison, *Statistical Models*](../lean-CKMA/References/Davison2003StatisticalModels-Cambridge.SerStatProbMath.pdf).
  Section 10.3.2 was read for deviance asymptotics.
- [Lauritzen, *Graphical Models*](../lean-CKMA/References/Lauritzen1996GraphicalModels-Oxford.StatSci17.pdf).
- [Mardia and Jupp, *Directional Statistics*](../lean-CKMA/References/MardiaJupp2000DirectionalStatistics-Wiley.SerProbStat.pdf).
- [Silvey, *Optimal Design*](../lean-CKMA/References/Silvey1980OptimalDesignIntroductionTheoryParameterEstimation-ChapmanHallMonogAPS.pdf).
- [Pukelsheim, *Optimal Design of Experiments*](../lean-CKMA/References/Pukelsheim2006OptimalDesignExperiments-SIAM.CAM50.pdf).
- [Fedorov and Hackl, *Model-Oriented Design of Experiments*](../lean-CKMA/References/FedorovHackl2025ModelOrientedDesignExperiments2ndEd-Springer.LNS209.pdf).
- [Cox and Reid, *The Theory of the Design of Experiments*](../lean-CKMA/References/CoxReid2000TheoryDesignExperiments-ChapmanHallCRC.MSAP86.pdf).
- [Bailey, *Design of Comparative Experiments*](../lean-CKMA/References/Bailey2008DesignComparativeExperiments-Cambridge.SerStatProbMath.pdf).
- [Cheng, *Theory of Factorial Design*](../lean-CKMA/References/Cheng2014TheoryFactorialDesignSingleMultiStratumExperiments-ChapmanHallCRC.MSAP131.pdf).
- [Hedayat, Sloane, and Stufken, *Orthogonal Arrays*](../lean-CKMA/References/HedayatSloaneStufken1999OrthogonalArraysTheoryApplications-Springer.SSS.pdf).
