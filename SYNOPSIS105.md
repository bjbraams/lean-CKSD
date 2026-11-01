# Synopsis: Linear models, multivariate analysis, experimental design, and causal inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-105).

This synopsis follows Section 105. Subdivision 105A is the linear model,
the analysis of variance and variance components, generalised linear
models, quantiles, finite mixtures, classical multivariate analysis,
graphical models, and directional data. Subdivision 105B is experimental
design, including block, factorial, and Latin-square designs;
finite-population survey sampling and allocation; and causal
inference: potential outcomes, randomized and observational studies,
interventions on directed graphical models, structural counterfactuals,
mediation, sensitivity, and discovery. Simultaneous confidence procedures
for the linear model are [SYNOPSIS101](SYNOPSIS101.md), items 60 and 61. Likelihood-ratio asymptotics are
[SYNOPSIS102](SYNOPSIS102.md), item 11. Missingness at random, the efficient influence function for a
missing mean, and semiparametric efficiency are [SYNOPSIS102](SYNOPSIS102.md), items 34, 35, and 37. The Cox
model is [SYNOPSIS106](SYNOPSIS106.md), item 30. High-dimensional covariance and sparsity are
[SYNOPSIS103](SYNOPSIS103.md).

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-105a"></a>

## 105A. Regression, Multivariate Analysis, and Graphical Models

### Regression, generalised linear models, and mixtures

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
  responses from an exponential dispersion family with $a(\varphi)=\varphi$,
  a twice differentiable link $g$ with $g'>0$, and $\mu_i$ in the interior
  of the mean space, the Fisher information for $\beta$ is
  $\varphi^{-1}X^\top WX$. Suppose now that the pairs $(x_i,Y_i)$ are
  independent and identically distributed, that the resulting model for
  one pair satisfies the hypotheses of SYNOPSIS102, item 3, at the true
  $\beta$, and that $J=\mathbb E[x_1x_1^\top w(x_1)]$ is nonsingular, where
  $w(x)=(d\mu/d\eta)^2/V(\mu)$ at $\eta=x^\top\beta$. Then a consistent root
  $\hat\beta$ of the likelihood equations satisfies
  $\sqrt n(\hat\beta-\beta)\Rightarrow N(0,\varphi J^{-1})$, and
  $\hat\varphi^{-1/2}J^{1/2}\sqrt n(\hat\beta-\beta)\Rightarrow N(0,I_p)$
  for every consistent estimator $\hat\varphi$ of $\varphi$. For two
  nested such models with $\varphi$ known, the difference of the scaled
  deviances (defined before item 21) is the likelihood-ratio statistic of
  SYNOPSIS102, item 11; under the hypotheses of that item and the smaller
  model it converges in distribution to chi-squared on the difference of
  the dimensions.

* **4. Quasi-likelihood.** Let the pairs $(x_i,Y_i)$ be independent and
  identically distributed, with $Y_i$ a random vector, let
  $\mu(x,\beta)$ be a mean function differentiable in $\beta$ with
  $D(x,\beta)=\partial\mu/\partial\beta$, and let $V(x)$ be a positive
  definite working covariance. Suppose the mean is correctly specified,
  $\mathbb E[Y_i\mid x_i]=\mu(x_i,\beta_0)$. Then the estimating function
  $\psi_\beta(x,y)=D(x,\beta)^\top V(x)^{-1}(y-\mu(x,\beta))$ has mean zero
  at $\beta_0$. If it satisfies the hypotheses of SYNOPSIS102, item 4, and
  $\hat\beta$ is a consistent root of $\sum_i\psi_\beta(x_i,Y_i)=0$, then
  $$\sqrt n(\hat\beta-\beta_0)\Rightarrow N\bigl(0,A^{-1}BA^{-1}\bigr),$$
  where $A=\mathbb E[D^\top V^{-1}D]$ and
  $B=\mathbb E[D^\top V^{-1}\mathop{\mathrm{Cov}}(Y\mid x)\,V^{-1}D]$, both
  evaluated at $\beta_0$, and $A$ is assumed nonsingular. If $V(x)$ equals
  $\mathop{\mathrm{Cov}}(Y\mid x)$, the sandwich $A^{-1}BA^{-1}$ reduces
  to $A^{-1}$.

The **check function** of order $\tau\in(0,1)$ is
$\rho_\tau(u)=u(\tau-1_{\{u<0\}})$. The $\tau$-quantile regression estimator
minimizes $\sum_{i=1}^n\rho_\tau(Y_i-x_i^\top\beta)$.

* **5. Quantile regression.** Let $Y_1,Y_2,\ldots$ be independent with
  fixed regressors $x_i\in\mathbb R^p$, and suppose the $\tau$-quantile of
  $Y_i$ is $\xi_i=x_i^\top\beta_\tau$ for every $i$. Assume that $Y_i$ has a
  density $f_i$, that the values $f_i(\xi_i)$ are bounded away from $0$
  and $\infty$, and that the $f_i$ are equicontinuous at the points
  $\xi_i$. Assume further that $n^{-1}\sum_{i\le n}x_ix_i^\top\to D_0$ and
  $n^{-1}\sum_{i\le n}f_i(\xi_i)x_ix_i^\top\to D_1$ with $D_0,D_1$ positive
  definite, and that $\max_{i\le n}\|x_i\|/\sqrt n\to0$. Then any
  minimizer $\hat\beta_\tau$ of $\sum_{i\le n}\rho_\tau(Y_i-x_i^\top\beta)$
  satisfies
  $$\sqrt n\,(\hat\beta_\tau-\beta_\tau)
  \Rightarrow N\bigl(0,\,\tau(1-\tau)\,D_1^{-1}D_0D_1^{-1}\bigr).$$

* **6. Finite normal mixtures.** A finite mixture of nondegenerate Gaussian
  distributions on $\mathbb R^d$, with distinct component parameters
  and strictly positive weights, is identifiable up to permutation of
  the component labels. With at least two components and unconstrained
  component covariance matrices, the likelihood is unbounded: a
  component mean placed at an observation, with that component's variance sent
  to zero, drives the likelihood to infinity.

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

* **8. Generalized least squares.** If the error covariance is
  $\sigma^2V$, with $V$ known positive definite, then
  $$\hat\beta_V=(X^\top V^{-1}X)^{-1}X^\top V^{-1}Y,\qquad
  \mathop{\mathrm{Cov}}(\hat\beta_V)
  =\sigma^2(X^\top V^{-1}X)^{-1}.$$
  It is the best linear unbiased estimator. Multiplication by $V^{-1/2}$
  reduces the problem to item 1. With Gaussian errors, items 2 and 10
  apply to the response $V^{-1/2}Y$ and the design $V^{-1/2}X$.

* **9. Partial regression.** Partition $X=(X_1,X_2)$ and let
  $M_1=I-P_{X_1}$. If $X$ has full column rank, the coefficient of $X_2$
  in the full least-squares fit is
  $$(X_2^\top M_1X_2)^{-1}X_2^\top M_1Y.$$
  Thus projecting both the response and the regressors off the nuisance
  columns yields the same coefficient and residual sum of squares. This
  is the Frisch–Waugh–Lovell theorem; its conditional-mean analogue is
  SYNOPSIS102, item 40.

* **10. Exact tests of nested linear models.** Let $P_0,P_1$ project onto
  nested model spaces of dimensions $r_0<r_1<n$. Under the smaller model
  and independent $N(0,\sigma^2)$ errors,
  $$\frac{\|(P_1-P_0)Y\|^2/(r_1-r_0)}
  {\|(I-P_1)Y\|^2/(n-r_1)}\sim F_{r_1-r_0,n-r_1}.$$
  The numerator and denominator sums of squares, divided by $\sigma^2$,
  are independent chi-squared variables. Under the larger model the
  numerator has noncentrality
  $\|(P_1-P_0)X\beta\|^2/\sigma^2$. A single estimable contrast gives
  the square of the usual Student $t$ statistic.

* **11. Leverage, deletion, and prediction error.** Write
  $H=X(X^\top X)^{-1}X^\top$, $h_i=H_{ii}$, and $e=(I-H)Y$.
  Then $0\le h_i\le1$, $\sum_i h_i=p$, and
  $\mathop{\mathrm{Cov}}(e)=\sigma^2(I-H)$. If $h_i<1$, deleting case
  $i$ preserves the design rank and gives
  $$\hat\beta_{(-i)}=\hat\beta-
  \frac{(X^\top X)^{-1}x_i e_i}{1-h_i},\qquad
  Y_i-x_i^\top\hat\beta_{(-i)}=\frac{e_i}{1-h_i}.$$
  Hence the leave-one-out squared prediction criterion is
  $n^{-1}\sum_i(e_i/(1-h_i))^2$ without refitting $n$ models. Under
  normal errors and $n>p+1$, let $s_{(-i)}^2$ be the residual sum of
  squares of the fit without case $i$, divided by $n-p-1$; the externally
  studentized residual $e_i/(s_{(-i)}\sqrt{1-h_i})$ has law $t_{n-p-1}$.

* **12. Ridge bias and variance.** For $\lambda>0$, the minimizer of
  $\|Y-Xb\|^2+\lambda\|b\|^2$ is
  $\hat\beta_\lambda=(X^\top X+\lambda I)^{-1}X^\top Y$, even for a
  rank-deficient design. If $\mathbb E\varepsilon=0$ and
  $\mathop{\mathrm{Cov}}\varepsilon=\sigma^2I$, its bias is
  $-\lambda(X^\top X+\lambda I)^{-1}\beta$ and its covariance is
  $$\sigma^2(X^\top X+\lambda I)^{-1}X^\top X
  (X^\top X+\lambda I)^{-1}.$$
  The fitted-value map has effective degrees of freedom
  $\mathop{\mathrm{tr}}[X(X^\top X+\lambda I)^{-1}X^\top]$.

* **13. Canonical likelihood and separation.** For a canonical generalized
  linear model with known dispersion, the log-likelihood in $\beta$ is
  concave, with negative Hessian $\varphi^{-1}X^\top W X$.
  It is strictly concave when $X$ has full column rank and all variance
  weights are positive; thus any finite score root is the unique maximum.
  In binary logistic regression, if a nonzero $b$ satisfies
  $(2Y_i-1)x_i^\top b\ge0$ for every $i$, with strict inequality for at
  least one observation, the likelihood increases along that direction
  and has no finite maximizer. Strict inequalities for every $i$ give
  complete separation. Concavity does not by itself establish existence.

* **14. Prediction in a linear mixed model.** Suppose
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

* **15. Distribution of quadratic forms.** Let $Y\sim N_n(\mu,\Sigma)$
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

* **16. Optimality of the $F$ test.** In the setting of item 10, the
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

* **17. Balanced two-way layout.** Let $Y_{ijk}=\eta_{ij}+e_{ijk}$ for
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

* **18. One-way variance components.** Here
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

* **19. Mallows' $C_p$.** In the model $Y=\mu+\varepsilon$ with
  $\mathbb E\varepsilon=0$ and $\mathop{\mathrm{Cov}}\varepsilon=\sigma^2I_n$,
  let a candidate submodel have an $n\times p$ design $X_p$ of full rank,
  projection $P_p$, and residual sum of squares $\mathrm{RSS}_p$. The
  model error $\mathrm{ME}_p=\|P_pY-\mu\|^2$ satisfies
  $$\mathbb E\,\mathrm{RSS}_p=\|(I-P_p)\mu\|^2+(n-p)\sigma^2
  =\mathbb E\,\mathrm{ME}_p+(n-2p)\sigma^2.$$
  Thus $\mathrm{RSS}_p+(2p-n)\sigma^2$ is unbiased for
  $\mathbb E\,\mathrm{ME}_p$. Mallows' statistic is
  $C_p=\mathrm{RSS}_p/\hat\sigma^2+2p-n$ for an estimator $\hat\sigma^2$
  of $\sigma^2$; with $\hat\sigma^2$ replaced by $\sigma^2$, its
  expectation is $\mathbb E\,\mathrm{ME}_p/\sigma^2$. For a submodel whose column
  space contains $\mu$, $\mathbb E\,\mathrm{RSS}_p/\sigma^2+2p-n=p$.
  Selection over many submodels by minimizing $C_p$ is governed by
  SYNOPSIS103, items 35 and 36.

### Fitting and assessing generalised linear models

* **20. Fisher scoring as iteratively reweighted least squares.** In
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
  Newton's method, and under item 13 a limit is the unique maximizer.

For a generalised linear model with $a_i(\varphi)=\varphi/w_i$, the
**deviance** of fitted means $\hat\mu$ is
$D(y;\hat\mu)=\varphi\cdot2\{\ell(y;y)-\ell(\hat\mu;y)\}$, where
$\ell(y;y)$ is the log-likelihood of the saturated model that fits each
observation exactly; $D/\varphi$ is the **scaled deviance**.

* **21. Deviance.** The deviance does not depend on $\varphi$. Summing
  over observations with unit prior weights, it equals $\sum(y-\hat\mu)^2$ for the normal model,
  $$2\sum\bigl\{y\log(y/\hat\mu)-(y-\hat\mu)\bigr\}$$
  for the Poisson model, and
  $$2\sum\bigl\{y\log(y/\hat\mu)+(m-y)\log((m-y)/(m-\hat\mu))\bigr\}$$
  for binomial counts out of $m$, with $0\log0=0$. Maximizing the
  likelihood minimizes the deviance, and for nested models fitted by
  maximum likelihood the deviances are additive, giving the analysis of
  deviance. Differences of scaled deviances obey item 3. For binary
  responses ($m=1$) with the logistic link, the deviance at the maximum
  likelihood estimate equals
  $-2\bigl\{\hat\mu^\top X\hat\beta+\sum_i\log(1-\hat\mu_i)\bigr\}$, a
  function of $X$ and $\hat\beta$ alone.

### Multivariate analysis, invariance, and graphical models

* **22. Wishart distribution and Hotelling's $T^2$.** Let $Z_1,\ldots,Z_n$ be
  independent $N_p(0,\Sigma)$ with $n\ge p$ and with $\Sigma$ positive
  definite. Then $W=\sum_{i=1}^n Z_iZ_i^\top$ has the Wishart distribution
  $W_p(n,\Sigma)$. For an independent normal sample of size $n\ge p+1$, the
  sample mean $\bar X$ and the sample covariance $S$ with divisor $n-1$ are
  independent, and $(n-1)S\sim W_p(n-1,\Sigma)$. Hotelling's statistic
  $T^2=n(\bar X-\mu)^\top S^{-1}(\bar X-\mu)$ satisfies
  $$\frac{n-p}{(n-1)p}\,T^2\sim F_{p,\,n-p}$$
  when the true mean is $\mu$.

* **23. Wilks's lambda.** In the multivariate normal linear model
  $Y=XB+U$, let $Y$ be $n\times p$, let $X$ be a fixed $n\times q$ matrix of
  rank $q$, and let the rows of $U$ be independent $N_p(0,\Sigma)$ with
  $\Sigma$ positive definite. For a hypothesis $CB=0$ with $C$ of size
  $h\times q$ and rank $h$, let $E=Y^\top(I-P_X)Y$ and let $H=E_0-E$, where
  $E_0$ is the residual matrix of the fit under the hypothesis; write
  $e=n-q\ge p$ and $\Lambda=\det(E)/\det(E+H)$. Under the hypothesis,
  $E\sim W_p(e,\Sigma)$ and $H\sim W_p(h,\Sigma)$ are independent, and
  $\Lambda$ has the law of $\prod_{i=1}^pV_i$ with $V_1,\ldots,V_p$
  independent and $V_i\sim\mathrm{Beta}\bigl((e+1-i)/2,\,h/2\bigr)$. With
  $k=e-(p-h+1)/2$, for each fixed $z$ and fixed $p,h$,
  $$P(-k\log\Lambda\le z)=P(\chi^2_{ph}\le z)+O(e^{-2})
  \qquad(e\to\infty).$$

* **24. Principal component eigenvalues.** Let $S_n$ be the sample covariance,
  with divisor $n$, of an independent normal sample in $\mathbb R^p$, and let
  $\lambda_j$ be a simple positive eigenvalue of the population covariance.
  The corresponding eigenvalue $\hat\lambda_j$ of $S_n$ satisfies
  $$\sqrt n\,(\hat\lambda_j-\lambda_j)\Rightarrow N(0,2\lambda_j^2).$$

* **25. Fisher's linear discriminant.** Consider two classes with priors
  $\pi_1>0$ and $\pi_2>0$, Gaussian conditional laws with means $\mu_1$
  and $\mu_2$, and a common positive definite covariance $\Sigma$. The Bayes rule for $0$–$1$ loss assigns an
  observation $x$ to class $1$ when
  $$(\mu_1-\mu_2)^\top\Sigma^{-1}\Bigl(x-\frac{\mu_1+\mu_2}2\Bigr)
  >\log\frac{\pi_2}{\pi_1}.$$
  The decision boundary is affine. If the class covariances are
  $\Sigma_1\ne\Sigma_2$, both positive definite, the Bayes rule assigns $x$
  to class $1$ when
  $$-\tfrac12(x-\mu_1)^\top\Sigma_1^{-1}(x-\mu_1)
  +\tfrac12(x-\mu_2)^\top\Sigma_2^{-1}(x-\mu_2)
  >\log\frac{\pi_2}{\pi_1}+\frac12\log\frac{\det\Sigma_1}{\det\Sigma_2},$$
  a quadratic inequality in $x$.

Let $G$ be an undirected graph with vertex set $\{1,\ldots,p\}$. A positive
continuous density on $\mathbb R^p$ satisfies the **pairwise Markov property**
when $X_i$ and $X_j$ are conditionally independent given the remaining
coordinates whenever $\{i,j\}$ is not an edge. It satisfies the **local
Markov property** when each $X_i$ is conditionally independent of the
coordinates outside $\{i\}\cup\mathrm{ne}(i)$ given $X_{\mathrm{ne}(i)}$,
where $\mathrm{ne}(i)$ is the set of neighbours of $i$. It satisfies the
**global Markov property** when, for disjoint vertex sets $A,B,S$ such that
every path from $A$ to $B$ meets $S$, $X_A$ and $X_B$ are conditionally
independent given $X_S$. The density **factorizes** over $G$ when it is a
product $\prod_C\psi_C(x_C)$ of nonnegative functions, one for each clique
$C$ of $G$, with $\psi_C$ depending only on the coordinates in $C$.

* **26. Undirected graphical models.** For a positive continuous density, the
  pairwise Markov property, the local Markov property, and the global Markov
  property are equivalent. A density that factorizes over $G$ satisfies the
  global Markov property; conversely, by the Hammersley–Clifford theorem, a
  positive continuous density with the pairwise Markov property factorizes
  over $G$ with positive factors. For a nondegenerate Gaussian law, $X_i$
  and $X_j$ are conditionally independent given the remaining coordinates
  if and only if the $(i,j)$ entry of the precision matrix vanishes.

The **von Mises–Fisher** density on the unit sphere $S^{p-1}$ is
$c_p(\kappa)\exp(\kappa\mu\cdot x)$, with $\|\mu\|=1$ and concentration
$\kappa\ge0$.

* **27. von Mises–Fisher model.** For an independent sample $X_1,\ldots,X_n$
  and fixed $\kappa>0$, if the resultant $\sum_{i=1}^n X_i$ is nonzero, the
  maximum likelihood estimator of the mean direction $\mu$ is its
  direction. On the
  circle, $\mathbb E[\cos(X-\mu)]=I_1(\kappa)/I_0(\kappa)$, and the likelihood
  equation for $\kappa$ equates this function to the mean resultant length.

### Covariance geometry and multivariate reduction

* **28. Gaussian covariance likelihood.** For a normal sample with unknown
  mean and positive definite covariance, if the centered sample spans
  $\mathbb R^p$, the maximum likelihood estimators are
  $$\hat\mu=\bar X,\qquad
  \hat\Sigma=\frac1n\sum_i(X_i-\bar X)(X_i-\bar X)^\top.$$
  If that scatter matrix is singular, the likelihood is unbounded over
  positive definite covariance matrices and there is no finite covariance
  maximizer in that space. This occurs almost surely when $n\le p$.
  Dividing by $n-1$ instead gives the unbiased covariance estimator whose
  Wishart law is item 22.

* **29. Canonical correlations.** For centered random vectors $(U,V)$
  with positive definite marginal covariances, the largest correlation
  between $a^\top U$ and $b^\top V$ is the largest singular value of
  $$\Sigma_{UU}^{-1/2}\Sigma_{UV}\Sigma_{VV}^{-1/2}.$$
  Subsequent singular values solve the same maximization with successive
  variates uncorrelated within each vector. They lie in $[0,1]$ and are
  unchanged by nonsingular linear transformations within $U$ or $V$.
  For a jointly Gaussian pair, all canonical correlations vanish if and
  only if $U$ and $V$ are independent.

* **30. Principal components and reconstruction.** For a centered vector
  with covariance eigenvalues $\lambda_1\ge\cdots\ge\lambda_p\ge0$,
  the first $k$ eigenvectors maximize captured variance
  $\mathop{\mathrm{tr}}(P\Sigma)$ among rank-$k$ orthogonal projections.
  The minimal mean squared reconstruction error is
  $\sum_{j>k}\lambda_j$. For a centered data matrix, truncating its singular
  value decomposition gives the best rank-$k$ approximation in Frobenius
  norm. Functional observations are covered by SYNOPSIS103, item 31;
  fixed-dimensional eigenvalue asymptotics are item 24.

### Wishart structure and correlation coefficients

* **31. Structure of the Wishart law.** Let $W\sim W_p(n,\Sigma)$ with
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

* **32. Sampling theory of correlation coefficients.** Let $r$ be the
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

* **33. Likelihood-ratio tests of sphericity and independence.** For
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
  $f=\sum_{i<j}p_ip_j$. With Box's multiplier
  $$m=N-\frac32-\frac{p^3-\sum_ip_i^3}{3\bigl(p^2-\sum_ip_i^2\bigr)},$$
  the distribution function of $-m\log\Lambda$ differs from that of
  $\chi^2_f$ by $O(N^{-2})$, for fixed $p_1,\ldots,p_k$. For $k=2$,
  $\Lambda=\prod_i(1-r_i^2)$, where the $r_i$ are the sample canonical
  correlations of item 29.

* **34. Invariant tests of a multivariate linear hypothesis.** In the
  setting of item 23 let $E$ be positive definite, and let
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
  reduce to the same exact $F$ test, as for Hotelling's $T^2$ in item 22.

The **orthogonal factor model** with $m$ factors states
$X=\mu+\Lambda f+u$, where $\Lambda$ is a $p\times m$ loading matrix,
$f$ has mean $0$ and covariance $I_m$, $u$ is uncorrelated with $f$ and
has mean $0$ and diagonal positive definite covariance $\Psi$. Then
$\mathop{\mathrm{Cov}}X=\Lambda\Lambda^\top+\Psi$.

* **35. Factor analysis and identification.** For every orthogonal
  $m\times m$ matrix $O$, the loadings $\Lambda O$ give the same
  covariance as $\Lambda$. Call $\Lambda$ **normalized** when
  $\Lambda^\top\Psi^{-1}\Lambda$ is diagonal with distinct diagonal
  entries in decreasing order; given $\Lambda\Lambda^\top$ and $\Psi$,
  a normalized $\Lambda$ is unique up to the signs of its columns.
  Suppose the true covariance $\Sigma=\Lambda_0\Lambda_0^\top+\Psi_0$ is
  attained by a unique pair $(\Lambda_0\Lambda_0^\top,\Psi_0)$ in the
  $m$-factor model, with $\Lambda_0$ normalized, and let $C$ be the sample
  covariance. If $C\to_P\Sigma$, the Gaussian maximum likelihood
  estimators $\hat\Psi$ of $\Psi$ and $\hat\Lambda$ of the normalized
  $\Lambda$, with suitable column signs, are consistent. Let
  $(\theta_{ij})=\Psi_0-\Lambda_0(\Lambda_0^\top\Psi_0^{-1}
  \Lambda_0)^{-1}\Lambda_0^\top$, with $\Lambda_0$ of rank $m$. If
  $\sqrt n(C-\Sigma)$ has a normal limit (as it does for a Gaussian
  sample) and the $p\times p$ matrix $(\theta_{ij}^2)$ of squared entries
  is nonsingular, then $\sqrt n(\hat\Lambda-\Lambda_0)$ and
  $\sqrt n(\hat\Psi-\Psi_0)$ have normal limits (Anderson and
  Rubin). If, moreover, the sample is Gaussian, then $-2$ times the log
  likelihood ratio for the $m$-factor model against an unrestricted
  covariance converges in distribution to chi-squared on
  $$\tfrac12\bigl[(p-m)^2-p-m\bigr]$$
  degrees of freedom, provided this number is positive. It equals the
  number $p(p+1)/2$ of covariance entries plus the $m(m-1)/2$ identifying
  conditions minus the $pm+p$ free parameters.

### Decomposable graphical models

An undirected graph is **decomposable** when every cycle of length at least
four has a chord. Its cliques can then be ordered so that each meets the
union of the earlier ones in a complete **separator**, and the multiset of
separators, with multiplicities $\nu(S)$, does not depend on the chosen
perfect order. For a matrix $B$ indexed by a subset $C$ of the vertices,
$[B]^V$ denotes the $p\times p$ matrix with $B$ in the block $C\times C$
and zeros elsewhere.

* **36. Decomposable models.** For a decomposable graph with cliques
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

<a id="synopsis-105b"></a>

## 105B. Experimental Design, Survey Sampling, and Causal Inference

Randomization connects experimental design, finite-population survey
sampling, and the identification and estimation of causal effects in
experiments and observational studies.

### Experimental design

For a regression with a continuous regressor $f(x)\in\mathbb R^p$ on a
compact design space $\mathcal X$ and a design given by a probability
measure $\xi$ on $\mathcal X$, the information matrix is
$M(\xi)=\int f(x)f(x)^\top\,\xi(dx)$.

* **37. Kiefer–Wolfowitz equivalence.** Assume $M(\xi^*)$ is nonsingular. The
  design $\xi^*$ maximizes $\det M(\xi)$ if and only if
  $$\max_x f(x)^\top M(\xi^*)^{-1}f(x)=p,$$
  with equality for every $x$ in the support of $\xi^*$. For a design
  criterion that is concave and strictly increasing with respect to the
  Loewner order on information matrices, and differentiable at the
  nonsingular matrix $M(\xi^*)$, the design $\xi^*$ is optimal if and only if
  the directional derivative of the criterion at $M(\xi^*)$ is nonpositive in
  the direction of every one-point design.

* **38. Randomization test.** Under the sharp null hypothesis that each unit's
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
$C=R-NK^{-1}N^\top$. The design is **connected** when the bipartite graph
joining each treatment to the blocks in which it occurs is connected.

* **39. Connectedness and estimability.** The design is connected if and only
  if $\mathop{\mathrm{rank}}(C)=v-1$. A treatment contrast $c^\top\tau$ is
  estimable if and only if $c$ lies in the column space of $C$.

An $N\times k$ array on $s$ symbols is an **orthogonal array of strength $t$**
when, in every set of $t$ columns, every possible $t$-tuple appears equally
often.

* **40. Orthogonal arrays.** Code each factor by $s-1$ mutually orthogonal
  contrast vectors on its $s$ levels, each orthogonal to the constant
  vector, and let an effect column of order $r$ be the run-wise product of
  one contrast for each of $r$ distinct factors (order $0$ being the
  constant column). In an array of strength $t$, distinct effect columns
  of orders $r,s$ are orthogonal when $r+s\le t$. In particular, a
  factorial model containing effects through order $q$ has mutually
  orthogonal columns when $2q\le t$; under independent homoscedastic
  errors its least-squares contrast estimators are uncorrelated. Effects
  of order less than $t$ need not all be mutually orthogonal, since their
  products can involve more than $t$ factors.

* **41. Balanced incomplete blocks.** In a balanced incomplete block design
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
  design attains this bound and, by item 41, has all $v-1$ positive
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
  polynomial of degree $d$. By item 37,
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
  strength $R-1$, as in item 40, and $R-1$ is its maximal strength.

### Survey sampling and finite populations

A **sampling design** is a probability law on the subsets $s$ of a finite
population $U=\{1,\ldots,N\}$. The values $y_i\in\mathbb R$ are fixed;
only $s$ is random. Put $I_i=1_{\{i\in s\}}$,
$\pi_i=\mathbb E I_i$, $\pi_{ij}=\mathbb E I_iI_j$, with
$\pi_{ii}=\pi_i$, and $\Delta_{ij}=\pi_{ij}-\pi_i\pi_j$.

* **72. Horvitz–Thompson estimation and design variance.** Assume
  $\pi_i>0$ for every unit. For the population total $t_y=\sum_i y_i$,
  $$\hat t_y=\sum_{i\in s}\frac{y_i}{\pi_i},\qquad
  \mathbb E\hat t_y=t_y,\qquad
  \mathop{\mathrm{Var}}(\hat t_y)
  =\sum_{i,j\in U}\Delta_{ij}\frac{y_i y_j}{\pi_i\pi_j}.$$
  If $\pi_{ij}>0$ for every distinct pair, an unbiased variance estimator is
  $$\hat V=\sum_{i,j\in s}\frac{\Delta_{ij}}{\pi_{ij}}
  \frac{y_i y_j}{\pi_i\pi_j}.$$
  If $|s|=n$ almost surely, the Sen–Yates–Grundy variance identity and,
  when all distinct pairs have positive inclusion probability, its
  unbiased estimator are
  $$\mathop{\mathrm{Var}}(\hat t_y)
  =-\frac12\sum_{i,j\in U}\Delta_{ij}
  \left(\frac{y_i}{\pi_i}-\frac{y_j}{\pi_j}\right)^2,\qquad
  \hat V_{\mathrm{SYG}}=-\frac12\sum_{i,j\in s}
  \frac{\Delta_{ij}}{\pi_{ij}}
  \left(\frac{y_i}{\pi_i}-\frac{y_j}{\pi_j}\right)^2.$$
  The latter is unbiased and is nonnegative when
  $\pi_{ij}\le\pi_i\pi_j$ for distinct pairs. Positive pairwise inclusion
  is needed for the displayed unbiased variance estimators, not for
  unbiased estimation of the total itself.

* **73. Simple and stratified random sampling; Neyman allocation.**
  For a uniform subset of size $1\le n\le N$ from $N\ge2$ units,
  the sample mean is unbiased for $\bar y=N^{-1}\sum_i y_i$ and
  $$\mathop{\mathrm{Var}}(\bar y_s)
  =\left(1-\frac nN\right)\frac{S^2}{n},\qquad
  S^2=\frac1{N-1}\sum_i(y_i-\bar y)^2.$$
  Partition the population into strata of sizes $N_h\ge2$, with
  $W_h=N_h/N$, and select independent uniform subsets of sizes
  $1\le n_h\le N_h$. With $\bar y_h,S_h^2$ the stratum population mean
  and variance, the estimator $\hat{\bar y}=\sum_h W_h\bar y_{s,h}$ is
  unbiased and has variance
  $$\sum_h W_h^2\left(1-\frac{n_h}{N_h}\right)\frac{S_h^2}{n_h}.$$
  For $n_h\ge2$, replacing each $S_h^2$ by the sample variance with
  divisor $n_h-1$ gives an unbiased variance estimator. For $S_h>0$
  and a fixed total $n=\sum_h n_h$, the continuous allocation problem
  has the solution
  $$n_h=\frac{nN_hS_h}{\sum_l N_lS_l},$$
  provided these values satisfy $1\le n_h\le N_h$. This is Neyman
  allocation for equal sampling costs; integer allocations require
  rounding or discrete optimization. Complete enumeration gives zero
  sampling variance. The one-stratum formula also supplies the sampling
  variance used in the randomized-experiment results below.

### Experiments, identification, and estimation

A unit has **potential outcomes** $Y(a)$ under each treatment level $a$ in
a finite set of treatments. The **stable unit treatment value assumption**
is that these potential outcomes do not depend on the treatments of other
units and that each treatment level has one version. The observed outcome
is the potential outcome of the treatment actually received. For a binary
treatment $A\in\{0,1\}$, the **average treatment effect** is
$\theta=\mathbb E[Y(1)-Y(0)]$.

Consider a finite population of $n$ units and a completely randomized
experiment that assigns treatment to a simple random subset of $n_1$ units
and control to the remaining $n_0=n-n_1$ units. Write
$\tau_i=Y_i(1)-Y_i(0)$, $\tau=n^{-1}\sum_{i=1}^n\tau_i$, and
$\bar Y(a)=n^{-1}\sum_{i=1}^n Y_i(a)$. The finite-population variances, with
divisor $n-1$, are
$$
S^2(a)=\frac1{n-1}\sum_{i=1}^n\bigl(Y_i(a)-\bar Y(a)\bigr)^2,
\qquad
S^2(\tau)=\frac1{n-1}\sum_{i=1}^n(\tau_i-\tau)^2.
$$
The difference-in-means estimator is $\hat\tau=\bar Y_1-\bar Y_0$, where
$\bar Y_a$ is the average of the observed outcomes in the arm of size $n_a$.

* **46. Neyman's theorem.** In a completely randomized experiment the
  potential outcomes are fixed and the only randomness is the assignment.
  Then $\mathbb E\hat\tau=\tau$ and
  $$\mathop{\mathrm{Var}}(\hat\tau)
  =\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}{n}.$$
  Let $\hat S^2(a)$ be the sample variance of the observed outcomes in arm
  $a$, with divisor $n_a-1$. The estimator
  $\hat V=\hat S^2(1)/n_1+\hat S^2(0)/n_0$ is conservative:
  $$\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)=S^2(\tau)/n\ge0,$$
  with equality if and only if $\tau_i=\tau$ for every unit.

Let $e_a(x)=P(A=a\mid X=x)$ and write
$m_a(x)=\mathbb E[Y\mid A=a,X=x]$. **Conditional ignorability** is the
independence $Y(a)\perp A\mid X$. **Positivity** at level $a$ is
$e_a(X)\ge\delta>0$ almost surely.

* **47. Identification by regression and by weighting.** Under conditional
  ignorability and positivity at level $a$, and if
  $\mathbb E|Y(a)|<\infty$,
  $$\mathbb E[Y(a)]
  =\mathbb E\bigl[m_a(X)\bigr]
  =\mathbb E\Bigl[\frac{1_{\{A=a\}}Y}{e_a(X)}\Bigr].$$
  For a binary treatment the average treatment effect is therefore
  $\mathbb E[m_1(X)-m_0(X)]$ when these hypotheses hold at both levels.

A measurable function $b$ of $X$ is a **balancing score** when
$A\perp X\mid b(X)$. The **propensity score** of a binary treatment is
$e(X)=P(A=1\mid X)$.

* **48. Propensity score.** Under conditional ignorability, $Y(a)$ is
  independent of $A$ given $e(X)$. The propensity score is a balancing
  score, and it is a function of every balancing score.

Write $\mu_a$ for a candidate regression and $e$ for a candidate propensity
score, write $e_0(X)=P(A=1\mid X)$ for the true propensity score (in items
49 and 56 the subscript $0$ marks the truth, not a treatment level), and set
$$
\varphi
=\mu_1(X)-\mu_0(X)
+\frac{A\bigl(Y-\mu_1(X)\bigr)}{e(X)}
-\frac{(1-A)\bigl(Y-\mu_0(X)\bigr)}{1-e(X)}.
$$

* **49. Doubly robust estimator of the average treatment effect.** Assume
  conditional ignorability and $e_0(X)\in[\delta,1-\delta]$. The expectation
  of $\varphi$ equals $\theta$ as soon as either $e=e_0$ and the functions
  $\mu_a$ are square-integrable, or $\mu_a=m_a$ for $a\in\{0,1\}$ and $e$
  is any measurable function with values in $[\delta,1-\delta]$. Let
  $\hat\theta$ be the cross-fitted average of $\varphi$, formed as in
  SYNOPSIS102, item 39, with fitted $\hat\mu_a$ and fitted $\hat e$ taking
  values in $[\delta,1-\delta]$, and suppose $\mathbb EY^2<\infty$. If
  $\|\hat\mu_a-m_a\|_2\to_P0$ and $\|\hat e-e_0\|_2\to_P0$, if
  $\|\hat\mu_a-m_a\|_2\,\|\hat e-e_0\|_2=o_P(n^{-1/2})$ for $a\in\{0,1\}$,
  and if the fitted functions $\varphi$ converge in $L^2$ to the true one,
  then
  $$\sqrt n(\hat\theta-\theta)=n^{-1/2}\sum_{i=1}^n
  \bigl(\varphi_0(O_i)-\theta\bigr)+o_P(1),$$
  where $\varphi_0$ is $\varphi$ with $\mu_a=m_a$ and $e=e_0$ and $O_i$ is
  the $i$-th observation; $\varphi_0-\theta$ is the efficient influence
  function. The missing-mean analogue is SYNOPSIS102, item 37, and
  the efficiency bound is SYNOPSIS102, item 34.

Let $Z\in\{0,1\}$ be an instrument, let $A(z)$ be the potential treatment,
and let $Y(z,a)$ be the potential outcome under instrument value $z$ and
treatment $a$; the observed values are $A=A(Z)$ and $Y=Y(Z,A)$.
**Exclusion** means $Y(0,a)=Y(1,a)$ for each $a$, and this common value is
written $Y(a)$. **Monotonicity** means
$A(1)\ge A(0)$ almost surely. A unit is a **complier** when
$A(1)>A(0)$.

* **50. Local average treatment effect.** Assume that
  $(Y(0),Y(1),A(0),A(1))$ is independent of $Z$, that exclusion and
  monotonicity hold, and that $P(A=1\mid Z=1)\ne P(A=1\mid Z=0)$. Then the
  Wald ratio equals the average treatment effect on the compliers:
  $$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
  {\mathbb E[A\mid Z=1]-\mathbb E[A\mid Z=0]}
  =\mathbb E\bigl[Y(1)-Y(0)\mid A(1)>A(0)\bigr].$$

### Stratified, paired, and regression-adjusted experiments

The sharp-null randomization test, valid in each of the designs below, is
item 38. In a **stratified randomized experiment** the units are
partitioned into strata $k=1,\ldots,K$ of sizes $n_{[k]}$, with
$\pi_{[k]}=n_{[k]}/n$, and independent completely randomized experiments with
$n_{[k]1}$ treated and $n_{[k]0}$ control units are run within the strata.
Write $\tau_{[k]}$, $\hat\tau_{[k]}$, and $S^2_{[k]}(\cdot)$ for the
quantities of item 46 within stratum $k$, and $\bar Y_{[k]}(a)$ for the
stratum mean of $Y(a)$.

* **51. Stratified experiments.** The stratified estimator
  $\hat\tau_S=\sum_k\pi_{[k]}\hat\tau_{[k]}$ is unbiased for $\tau$, with
  $$\mathop{\mathrm{Var}}(\hat\tau_S)=\sum_{k=1}^K\pi_{[k]}^2\Bigl(
  \frac{S^2_{[k]}(1)}{n_{[k]1}}+\frac{S^2_{[k]}(0)}{n_{[k]0}}
  -\frac{S^2_{[k]}(\tau)}{n_{[k]}}\Bigr).$$
  If every arm of every stratum has at least two units, the estimator
  $\hat V_S=\sum_k\pi_{[k]}^2\bigl(\hat S^2_{[k]}(1)/n_{[k]1}
  +\hat S^2_{[k]}(0)/n_{[k]0}\bigr)$ is conservative, exactly as in item 46.
  If the treated fraction $n_{[k]1}/n_{[k]}$ equals $n_1/n$ in every
  stratum, then $\hat\tau_S$ equals the difference in means $\hat\tau$.
  Let $\mathop{\mathrm{Var}}_{\mathrm{CR}}(\hat\tau)$ be the variance of
  item 46 under complete randomization with $n_1$ treated units. Then
  $$\mathop{\mathrm{Var}}_{\mathrm{CR}}(\hat\tau)
  -\mathop{\mathrm{Var}}(\hat\tau_S)=\frac n{n-1}\,G
  -\frac1{n-1}\sum_{k=1}^K(1-\pi_{[k]})\Bigl(
  \frac{S^2_{[k]}(1)}{n_1}+\frac{S^2_{[k]}(0)}{n_0}
  -\frac{S^2_{[k]}(\tau)}{n}\Bigr),$$
  where
  $$G=\sum_{k=1}^K\frac{\pi_{[k]}}n\Bigl\{\Bigl(\frac{n_0}{n_1}\Bigr)^{1/2}
  \bigl(\bar Y_{[k]}(1)-\bar Y(1)\bigr)+\Bigl(\frac{n_1}{n_0}\Bigr)^{1/2}
  \bigl(\bar Y_{[k]}(0)-\bar Y(0)\bigr)\Bigr\}^2\ge0.$$

In a **matched-pairs experiment** there are $n$ pairs of units, and within
each pair one unit is assigned to treatment by an independent fair coin. Let
$\tau_i$ be the average of the two unit effects in pair $i$,
$\tau=n^{-1}\sum_i\tau_i$, and let $\hat\tau_i$ be the treated-minus-control
difference in pair $i$, with $\hat\tau=n^{-1}\sum_i\hat\tau_i$.

* **52. Matched-pairs experiments.** The estimator $\hat\tau$ is unbiased for
  $\tau$. Although no within-pair variance can be estimated, the
  between-pair estimator $\hat V=\{n(n-1)\}^{-1}\sum_i(\hat\tau_i-\hat\tau)^2$
  is conservative:
  $$\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)
  =\frac1{n(n-1)}\sum_{i=1}^n(\tau_i-\tau)^2\ge0,$$
  with equality when the pair effects $\tau_i$ are all equal. The estimator
  and its variance estimate coincide with the one-sample $t$ analysis of the
  differences $\hat\tau_i$.

In the completely randomized experiment of item 46, let $x_i$ be fixed
covariate vectors centered so that $\bar x=0$. **Fisher's covariance-adjusted
estimator** $\hat\tau_F$ is the coefficient of the treatment indicator in the
least-squares fit of $Y$ on $(1,A,x)$. **Lin's estimator** $\hat\tau_L$ is the
coefficient of $A$ in the least-squares fit of $Y$ on $(1,A,x,Ax)$.

* **53. Regression adjustment in randomized experiments.** For fixed
  vectors $b_1,b_0$, the adjusted difference in means
  $$\hat\tau(b_1,b_0)=n_1^{-1}\sum_iA_i(Y_i-b_1^\top x_i)
  -n_0^{-1}\sum_i(1-A_i)(Y_i-b_0^\top x_i)$$
  is unbiased for $\tau$, with the variance of item 46 computed from the
  adjusted potential outcomes $Y_i(a)-b_a^\top x_i$. Lin's estimator is
  $\hat\tau(\hat b_1,\hat b_0)$ with $\hat b_a$ the least-squares slope of $Y$
  on $x$ in arm $a$; it equals the difference of the two arm-wise fitted
  intercepts. Consider a sequence of finite populations with a fixed
  covariate dimension, in which $n_1/n\to e\in(0,1)$, the finite-population
  means and covariances of $(x_i,Y_i(1),Y_i(0))$ converge to finite limits
  with the limiting covariance of $x_i$ nonsingular, and the
  finite-population fourth moments of these quantities are bounded. Then
  $\sqrt n(\hat\tau_L-\tau)\Rightarrow N(0,v_L)$, $\sqrt n(\hat\tau-\tau)$
  and $\sqrt n(\hat\tau_F-\tau)$ have normal limits with variances at
  least $v_L$, and $n$ times the squared heteroscedasticity-robust
  (Eicker–Huber–White) standard error of $\hat\tau_L$ converges in
  probability to a limit at least $v_L$. No linear model for the potential
  outcomes is assumed.

### Treated-unit effects and instrumental variables

* **54. Average effect on the treated.** For a binary treatment with
  propensity score $e$, suppose only $Y(0)\perp A\mid X$ and $e(X)<1$ almost
  surely. Then the average treatment effect on the treated,
  $\tau_T=\mathbb E[Y(1)-Y(0)\mid A=1]$, is identified by
  $$\tau_T=\mathbb E[Y\mid A=1]-\mathbb E\bigl[m_0(X)\mid A=1\bigr]
  =\mathbb E[Y\mid A=1]-\frac{\mathbb E\bigl[(1-A)\,e(X)Y/(1-e(X))\bigr]}{P(A=1)},$$
  provided $P(A=1)>0$ and $\mathbb E|Y(0)|$ and $\mathbb E|Y(1)|$ are
  finite.

In the **linear instrumental-variable model**
$Y=D^\top\beta+\varepsilon$, the regressor vector $D$ may be correlated with
$\varepsilon$, and an instrument vector $Z$ satisfies $\mathbb E[Z\varepsilon]=0$,
with $\mathbb E[ZZ^\top]$ nonsingular and $\mathbb E[ZD^\top]$ of full column
rank. Observed and exogenous regressors are included in both $D$ and $Z$.
The **two-stage least-squares estimator** regresses $D$ on $Z$ by least
squares and then $Y$ on the fitted values $\hat D$.

* **55. Two-stage least squares.** For independent copies with finite second
  moments,
  $$\hat\beta_{\mathrm{tsls}}=\beta+\Bigl(\sum_i\hat D_i\hat D_i^\top\Bigr)^{-1}
  \sum_i\hat D_i\varepsilon_i\to_P\beta.$$
  Write $Q_{ZZ}=\mathbb E[ZZ^\top]$, $Q_{ZD}=\mathbb E[ZD^\top]$,
  $H=Q_{ZD}^\top Q_{ZZ}^{-1}Q_{ZD}$, and
  $\Omega=\mathbb E[\varepsilon^2ZZ^\top]$.
  If $Z$ and $D$ have finite fourth moments and $\Omega$ is finite, then
  $$\sqrt n(\hat\beta_{\mathrm{tsls}}-\beta)\Rightarrow N\bigl(0,\;
  H^{-1}Q_{ZD}^\top Q_{ZZ}^{-1}\,\Omega\,Q_{ZZ}^{-1}Q_{ZD}H^{-1}\bigr),$$
  and this covariance is estimated consistently by replacing the moments
  with sample moments and $\varepsilon_i$ with the residuals
  $Y_i-\hat\beta^\top_{\mathrm{tsls}}D_i$. When
  $D$ and $Z$ have the same dimension, it equals the instrumental-variable
  estimator $(\sum_iZ_iD_i^\top)^{-1}\sum_iZ_iY_i$. With one endogenous
  regressor and one instrument it equals the ratio of the reduced-form
  coefficients of $Z$ for $Y$ and for $D$; for binary $Z$ and $D$ without
  covariates this is the sample Wald ratio, whose probability limit under
  the assumptions of item 50 is the complier effect of that item, whether
  or not the linear model holds.

### Efficiency, partial identification, and design-based identification

* **56. Efficient variance for an average treatment effect.** Under the
  assumptions of item 49, write $\sigma_a^2(X)=\mathop{\mathrm{Var}}(Y\mid
  A=a,X)$ and suppose the following expression is finite. In the
  unrestricted observed-data model the efficient influence function is
  $\varphi-\theta$ with true nuisance functions, and its variance is
  $$\mathop{\mathrm{Var}}(m_1(X)-m_0(X))+
  \mathbb E\left[\frac{\sigma_1^2(X)}{e_0(X)}+
  \frac{\sigma_0^2(X)}{1-e_0(X)}\right].$$
  Under the conditions stated in item 49, the cross-fitted estimator
  $\hat\theta$ of that item satisfies $\sqrt n(\hat\theta-\theta)\Rightarrow
  N(0,v)$ with $v$ this variance.

* **57. Bounds without ignorability.** Suppose only consistency and
  $0\le Y(a)\le1$. Write $p=P(A=1)\in(0,1)$ and
  $\mu_a=\mathbb E[Y\mid A=a]$. Then the average treatment effect lies in
  $$[p\mu_1-(1-p)\mu_0-p,\quad
  p\mu_1+(1-p)-(1-p)\mu_0].$$
  These bounds are sharp: every value in the interval is compatible with
  the observed law.

* **58. Regression discontinuity.** Let treatment be
  $A=1_{\{X\ge c\}}$, with observed outcome $Y=Y(A)$.
  If $x\mapsto\mathbb E[Y(a)\mid X=x]$ has a version continuous at $c$
  for each $a$, then the effect at the cutoff is identified by
  $$\mathbb E[Y(1)-Y(0)\mid X=c]
  =\lim_{x\downarrow c}\mathbb E[Y\mid X=x]
  -\lim_{x\uparrow c}\mathbb E[Y\mid X=x].$$
  Here $P(c-h<X<c)>0$ and $P(c\le X<c+h)>0$ for every $h>0$, the
  conditional expectations on the right are given by the continuous
  versions of $\mathbb E[Y(1)\mid X=x]$ for $x\ge c$ and $\mathbb E[Y(0)\mid X=x]$
  for $x<c$, and the left side is the difference of these versions at $c$.

* **59. Difference in differences.** On one population, observed at two
  periods $t=0,1$ (panel data), let $G$ be a group indicator and let
  $Y_t(0),Y_t(1)$ be the potential outcomes at time $t$. Suppose only group
  $G=1$ receives treatment, at $t=1$: $Y_0=Y_0(0)$ (no anticipation) and
  $Y_1=Y_1(G)$ (consistency). Assume $0<P(G=1)<1$, integrable potential
  outcomes, and parallel untreated mean trends:
  $$\mathbb E[Y_1(0)-Y_0(0)\mid G=1]
  =\mathbb E[Y_1(0)-Y_0(0)\mid G=0].$$
  Then the average effect on the treated at time 1,
  $\mathbb E[Y_1(1)-Y_1(0)\mid G=1]$, equals
  $$\{\mathbb E[Y_1\mid G=1]-\mathbb E[Y_0\mid G=1]\}
  -\{\mathbb E[Y_1\mid G=0]-\mathbb E[Y_0\mid G=0]\}.$$

### Sensitivity to unmeasured confounding and mediation

Let the treatment $A$ and outcome $Y$ be binary, let $U$ be a binary
unmeasured confounder with $A\perp Y\mid(X,U)$, and, at a fixed value $x$ of
the measured covariates, write
$$\mathrm{rr}_{AU}=\frac{P(U=1\mid A=1,x)}{P(U=1\mid A=0,x)},\qquad
\mathrm{rr}_{UY}=\frac{P(Y=1\mid U=1,x)}{P(Y=1\mid U=0,x)},\qquad
\mathrm{rr}^{\mathrm{obs}}=\frac{P(Y=1\mid A=1,x)}{P(Y=1\mid A=0,x)}.$$

* **60. Cornfield inequalities and the E-value.** If
  $\mathrm{rr}^{\mathrm{obs}}>1$, $\mathrm{rr}_{AU}>1$, and
  $\mathrm{rr}_{UY}>1$, then
  $$\mathrm{rr}^{\mathrm{obs}}\le
  \frac{\mathrm{rr}_{AU}\,\mathrm{rr}_{UY}}{\mathrm{rr}_{AU}+\mathrm{rr}_{UY}-1}.$$
  Consequently both $\mathrm{rr}_{AU}$ and $\mathrm{rr}_{UY}$ are at least
  $\mathrm{rr}^{\mathrm{obs}}$ (Cornfield's inequality), and
  $$\max(\mathrm{rr}_{AU},\mathrm{rr}_{UY})\ge
  \mathrm{rr}^{\mathrm{obs}}+\sqrt{\mathrm{rr}^{\mathrm{obs}}
  (\mathrm{rr}^{\mathrm{obs}}-1)}.$$
  The right side is the **E-value** of Ding and VanderWeele. At least one
  of the two confounding associations must reach it; if the two
  associations are equal, both must reach it. One association may be
  smaller when the other is sufficiently larger, subject to the joint
  bound above. Both must separately reach $\mathrm{rr}^{\mathrm{obs}}$,
  which is the weaker Cornfield bound. The case
  $\mathrm{rr}^{\mathrm{obs}}<1$ follows by relabeling the
  treatment levels. Item 66 is the corresponding design-based sensitivity
  analysis for matched pairs.

For a binary treatment $A$, a mediator $M$, and outcome $Y$, let $M(a)$ be the
potential mediator and $Y(a,m)$ the potential outcome with consistency
$M=M(A)$ and $Y=Y(A,M)$. Write $Y(a,M(a'))$ for the nested potential outcome
and define the **natural direct** and **natural indirect effects**
$$\mathrm{NDE}=\mathbb E\bigl[Y(1,M(0))-Y(0,M(0))\bigr],\qquad
\mathrm{NIE}=\mathbb E\bigl[Y(1,M(1))-Y(1,M(0))\bigr],$$
whose sum is the total effect $\mathbb E[Y(1,M(1))-Y(0,M(0))]$.

* **61. Mediation formula.** Assume, for all $a,a',m$, that
  $A\perp Y(a,m)\mid X$, $M\perp Y(a,m)\mid(X,A)$, $A\perp M(a)\mid X$, and the
  cross-world independence $Y(a,m)\perp M(a')\mid X$, together with
  positivity of the conditioning events. Then, for discrete $M$ and $X$,
  $$\mathbb E\bigl[Y(a,M(a'))\bigr]=\sum_x\sum_m
  \mathbb E[Y\mid A=a,M=m,X=x]\,P(M=m\mid A=a',X=x)\,P(X=x),$$
  with integrals against conditional densities in general. Hence the natural
  direct and indirect effects are identified. All four conditions hold in
  a structural causal model $A=f_A(X,\varepsilon_A)$,
  $M=f_M(X,A,\varepsilon_M)$, $Y=f_Y(X,A,M,\varepsilon_Y)$ with
  $X,\varepsilon_A,\varepsilon_M,\varepsilon_Y$ mutually independent, where
  $M(a)=f_M(X,a,\varepsilon_M)$ and $Y(a,m)=f_Y(X,a,m,\varepsilon_Y)$.

### Graphical interventions

Let $G$ be a directed acyclic graph on a finite set $V$ of vertices, and let
$\xi=(\xi_v)_{v\in V}$ have a law with density $p$ with respect to a product
measure. The law **factorizes recursively** along $G$ when
$p(x)=\prod_{v\in V}p(x_v\mid x_{\mathrm{pa}(v)})$, where $\mathrm{pa}(v)$
is the set of parents of $v$. It satisfies the **local directed Markov
property** when each $\xi_v$ is conditionally independent of the
variables of its nondescendants given $\xi_{\mathrm{pa}(v)}$. A path is
**blocked** by $W$ if at least one noncollider on the path belongs to $W$,
or at least one collider has no descendant, including itself, in $W$. Two
disjoint vertex sets are **$d$-separated** by a third if every path between
them is blocked. The **global Markov property** says that $d$-separation
implies the corresponding conditional independence.

* **62. Directed Markov properties.** For a law with a density as above,
  recursive factorization along $G$, the local directed Markov property,
  and the global Markov property are equivalent. The undirected
  Hammersley–Clifford theorem is item 26.

In items 63 and 64 the variables are discrete, the law $P$ of the vertex
variables factorizes recursively along $G$, and $X,Y,Z,W$ denote disjoint
sets of vertices. The intervention $\mathop{\mathrm{do}}(X=x)$ is defined
by the truncated factorization
$P(v\mid\mathop{\mathrm{do}}(x))=\prod_{u\notin X}P(v_u\mid v_{\mathrm{pa}(u)})$
for configurations $v$ consistent with $x$, and $0$ otherwise; conditional
probabilities appearing in the formulas are assumed to have positive
conditioning events. Write $G_{\bar X}$ for the
graph with arrows into $X$ removed and $G_{\underline Z}$ for the graph
with arrows out of $Z$ removed. A set $Z$ satisfies the **back-door
criterion** relative to $(X,Y)$ when no vertex of $Z$ is a descendant of
$X$ and $Z$ blocks every path from $X$ to $Y$ that starts with an arrow
into $X$ (a **back-door path** from $X$). A set $Z$ satisfies the
**front-door criterion** when $Z$ intercepts every directed path from $X$
to $Y$, every back-door path from $X$ to $Z$ is blocked, and $X$ blocks
every back-door path from $Z$ to $Y$.

* **63. Back-door and front-door formulae.** If $Z$ satisfies the back-door
  criterion relative to $(X,Y)$, then
  $$P\bigl(y\mid\mathop{\mathrm{do}}(x)\bigr)
  =\sum_z P(y\mid x,z)\,P(z).$$
  If $Z$ satisfies the front-door criterion, then
  $$P\bigl(y\mid\mathop{\mathrm{do}}(x)\bigr)
  =\sum_z P(z\mid x)\sum_{x'}P(y\mid x',z)\,P(x').$$

* **64. Rules of the do-calculus.** Let $X,Y,Z,W$ be disjoint sets of
  vertices. Write $Z(W)$ for the vertices of $Z$ that are not ancestors of
  any vertex of $W$ in $G_{\bar X}$. Then
  $$
  \begin{aligned}
  P(y\mid\mathop{\mathrm{do}}(x),z,w)
  &=P(y\mid\mathop{\mathrm{do}}(x),w)
  &&\text{if }(Y\perp Z\mid X,W)_{G_{\bar X}},\\
  P(y\mid\mathop{\mathrm{do}}(x),\mathop{\mathrm{do}}(z),w)
  &=P(y\mid\mathop{\mathrm{do}}(x),z,w)
  &&\text{if }(Y\perp Z\mid X,W)_{G_{\bar X\underline Z}},\\
  P(y\mid\mathop{\mathrm{do}}(x),\mathop{\mathrm{do}}(z),w)
  &=P(y\mid\mathop{\mathrm{do}}(x),w)
  &&\text{if }(Y\perp Z\mid X,W)_{G_{\bar X,\overline{Z(W)}}}.
  \end{aligned}
  $$
  These are Pearl's Theorem 3.4.1. Now let some vertices be unobserved,
  and let $X,Y$ be disjoint sets of observed vertices. The query
  $P(y\mid\mathop{\mathrm{do}}(x))$ is **identifiable** when it takes
  the same value for any two laws factorizing recursively along $G$ whose
  marginal laws of the observed vertices coincide and are positive. It is
  identifiable if and only if finitely many applications of the three
  rules and of the ordinary rules of probability transform it into an
  expression in that marginal law alone. The same equivalence holds for
  conditional queries $P(y\mid\mathop{\mathrm{do}}(x),z)$, with $Z$ a
  further disjoint set of observed vertices, when $G$ is semi-Markovian
  (every unobserved vertex is a root with exactly two children, both
  observed) and identifiability is required over all laws factorizing
  along $G$, among those with $P(z\mid\mathop{\mathrm{do}}(x))>0$.

Let $A_t$ be a treatment at time $t=0,\ldots,T$, let $H_t$ be the history
available just before $A_t$, and let $Y(\bar a)$ be the outcome under a
treatment regime $\bar a=(a_0,\ldots,a_T)$. **Sequential exchangeability**
is the independence
$Y(\bar a)\perp A_t\mid H_t,\,A_{0:t-1}=a_{0:t-1}$ at each $t$.
**Sequential positivity** is a lower bound, uniform in $t$, on the
conditional probability of $A_t=a_t$ given the observed past.

* **65. Longitudinal $g$-formula.** Write
  $H_t=(L_0,A_0,L_1,\ldots,A_{t-1},L_t)$, where $L_0$ is baseline
  and $L_t$ is measured before $A_t$. Under consistency, sequential
  exchangeability, and sequential positivity, for discrete covariates,
  $$\mathbb E[Y(\bar a)]
  =\sum_{\bar l} \mathbb E[Y\mid\bar L_T=\bar l,\bar A_T=\bar a]
  P(L_0=l_0)\prod_{t=1}^T
  P(L_t=l_t\mid\bar L_{t-1}=\bar l_{t-1},
  \bar A_{t-1}=\bar a_{t-1}).$$
  Integrals against the corresponding conditional kernels replace sums
  for general covariates. Equivalently, with $Q_{T+1}=Y$ and
  $Q_t=\mathbb E[Q_{t+1}\mid\bar L_t,\bar A_t=\bar a_t]$ for
  $t=T,T-1,\ldots,0$, each $Q_t$ being a function of $\bar L_t$, one has
  $\mathbb E[Y(\bar a)]=\mathbb E[Q_0]$.

For a matched-pair observational study, Rosenbaum's model with parameter
$\Gamma\ge1$ bounds the ratio of the two units' treatment odds within
each pair between $1/\Gamma$ and $\Gamma$. Conditional on one treated
unit per pair, assignments in different pairs are independent and each
assignment probability lies between $1/(1+\Gamma)$ and $\Gamma/(1+\Gamma)$.

* **66. Sensitivity of a randomization test.** Assume the sharp null
  hypothesis of item 38, so that the responses are fixed, and let $d_i$ be
  the treated-minus-control difference in pair $i$. Consider a statistic
  $T=\sum_iq_i1_{\{d_i>0\}}$ with fixed weights $q_i\ge0$ that depend
  only on $|d_1|,\ldots,|d_n|$, such as the Wilcoxon signed-rank
  statistic. Let $T^+=\sum_iq_iB_i$, where $B_i=0$ if $d_i=0$ and otherwise
  the $B_i$ are independent Bernoulli variables with success probability
  $\Gamma/(1+\Gamma)$. Then under every assignment law of the sensitivity
  model, $P(T\ge t)\le P(T^+\ge t)$ for every $t$, so
  $\bar p=P(T^+\ge t)$ evaluated at the observed value $t$ of $T$ is a
  valid $p$-value: $P(\bar p\le\alpha)\le\alpha$ for every $\alpha$.
  At $\Gamma=1$, $\bar p$ is the randomization $p$-value of the paired
  experiment.

* **67. Markov equivalence of directed graphs.** Two directed acyclic
  graphs have the same $d$-separation relations if and only if they have
  the same skeleton and the same unshielded colliders
  $i\to j\leftarrow k$ with $i,k$ nonadjacent; such graphs are called
  **Markov equivalent**. A law is **faithful** to $G$ when its conditional
  independences are exactly those implied by $d$-separation in $G$. If a
  law is faithful to $G$, the directed acyclic graphs to which it is
  faithful are exactly the graphs Markov equivalent to $G$.

### Structural counterfactuals and time-varying treatments

A **structural causal model** consists of background variables $U$ with a
probability law, endogenous variables $V_1,\ldots,V_n$, and functions
$v_i=f_i(\mathrm{pa}_i,u_i)$ that determine $V$ uniquely from $U$; in the
recursive case the parent relation is a directed acyclic graph. The
intervention $\mathop{\mathrm{do}}(X=x)$ replaces the equations of $X$ by
$X=x$, and the **potential response** $Y_x(u)$ is the value of $Y$ in the
modified system. These responses are potential outcomes in the sense of the
opening paragraph, and consistency $Y_X=Y$ holds by construction. For binary
$X$ and $Y$, write $y,y'$ and $x,x'$ for the two values, $y_x$ for the event
$Y_x=y$, and define the **probability of necessity**
$\mathrm{PN}=P(y'_{x'}\mid x,y)$, the **probability of sufficiency**
$\mathrm{PS}=P(y_x\mid x',y')$, and the **probability of necessity and
sufficiency** $\mathrm{PNS}=P(y_x,y'_{x'})$. The treatment is **exogenous**
when $(Y_x,Y_{x'})\perp X$, and $Y$ is **monotone** in $X$ when the event
$y_{x'}\cap y'_x$ is empty.

* **68. Probabilities of causation.** Under exogeneity,
  $$\max\bigl\{0,P(y\mid x)-P(y\mid x')\bigr\}\le\mathrm{PNS}\le
  \min\bigl\{P(y\mid x),P(y'\mid x')\bigr\},$$
  both bounds are sharp, and
  $\mathrm{PN}=\mathrm{PNS}/P(y\mid x)$ and $\mathrm{PS}=\mathrm{PNS}/P(y'\mid x')$.
  If in addition $Y$ is monotone in $X$, all three are identified, with
  $\mathrm{PNS}=P(y\mid x)-P(y\mid x')$ and the excess risk ratio
  $$\mathrm{PN}=\frac{P(y\mid x)-P(y\mid x')}{P(y\mid x)}.$$
  Under monotonicity alone, without exogeneity,
  $\mathrm{PNS}=P(y_x)-P(y_{x'})$, $\mathrm{PN}=(P(y)-P(y_{x'}))/P(x,y)$,
  and $\mathrm{PS}=(P(y_x)-P(y))/P(x',y')$, whenever the denominators
  are positive.

In the setting of item 65, write
$e_t(a_t\mid H_t,\bar a_{t-1})=P(A_t=a_t\mid H_t,A_{0:t-1}=\bar a_{t-1})$ for
the treatment probabilities. A **marginal structural model** is a
parametric model $\mathbb E[Y(\bar a)\mid L_0]=f(\bar a,L_0;\beta)$ for the
regime-specific means.

* **69. Inverse probability weighting for time-varying treatments.**
  Under consistency, sequential exchangeability, and sequential positivity,
  $$\mathbb E[Y(\bar a)]=\mathbb E\Bigl[\frac{1_{\{\bar A_T=\bar a\}}\,Y}
  {\prod_{t=0}^Te_t(a_t\mid H_t,\bar a_{t-1})}\Bigr],$$
  which equals the $g$-formula of item 65. If the marginal structural model
  is correct, its parameter is a minimizer
  $$\beta=\mathop{\mathrm{arg\,min}}_b\sum_{\bar a}\mathbb E\Bigl[
  \frac{1_{\{\bar A_T=\bar a\}}}{\prod_te_t(a_t\mid H_t,\bar a_{t-1})}
  \bigl(Y-f(\bar a,L_0;b)\bigr)^2\Bigr],$$
  for finitely valued treatments, the sum running over all regimes, provided
  $\mathbb E[Y(\bar a)^2]<\infty$. Multiplying the weights by a function
  of $(\bar a,L_0)$,
  such as the product of the marginal treatment probabilities, gives
  **stabilized weights**; when $f$ is correct and the multiplier is
  positive and bounded, $\beta$ remains a minimizer of the reweighted criterion.

### Causal discovery

* **70. Skeleton and colliders from conditional independences.** In a
  directed acyclic graph, two vertices are adjacent if and only if no subset
  of the other vertices $d$-separates them, and two nonadjacent vertices are
  $d$-separated by the parents of one of them. If $i-j-k$ is a path in the
  skeleton with $i,k$ nonadjacent and $S$ is any set $d$-separating $i$ and
  $k$, then $i\to j\leftarrow k$ if and only if $j\notin S$. Consequently,
  if the law satisfies the global Markov property along $G$ and is faithful
  to $G$, its conditional independences determine the skeleton and the
  unshielded colliders of $G$, and hence the Markov equivalence class of
  item 67. Given exact answers to conditional-independence queries, the PC
  algorithm, which deletes the edge $i-j$ as soon as some subset of the
  current neighbours of $i$ or of $j$ renders $i$ and $j$ conditionally
  independent, searching such subsets in order of increasing size, and then
  orients $i\to j\leftarrow k$ for each such triple with $j$ outside the
  recorded separating set, returns the skeleton and the unshielded
  colliders of $G$.

* **71. Identifiability of restricted structural equation models.** Suppose
  $X_j=\sum_{k\in\mathrm{pa}(j)}\beta_{jk}X_k+N_j$ along a directed acyclic
  graph $G$, with jointly independent noises and $\beta_{jk}\ne0$ for every
  edge. If the noises are non-Gaussian with strictly positive densities
  (the linear non-Gaussian acyclic model), or if they are Gaussian with a
  common variance, then $G$ is identifiable from the joint distribution.
  The same holds for $X_j=f_j(X_{\mathrm{pa}(j)})+N_j$ with Gaussian noises and
  three times differentiable functions $f_j$ that are nonlinear in each
  argument. By contrast, linear Gaussian models with unrestricted variances
  identify only the Markov equivalence class.

## Reference guide

### Correspondence with the subdivisions

- **[105A](#synopsis-105a)**: Rao, Scheffé, Seber and Lee, and Christensen
  carry the linear model, quadratic forms, and the analysis of variance.
  McCullagh and Nelder carry generalised linear models and quasi-likelihood.
  Koenker carries quantile regression. McLachlan and Peel carry finite
  mixtures. Searle, Casella, and McCulloch carry residual maximum likelihood
  in the linear model. Anderson, Muirhead, Mardia, Kent, and Bibby, Eaton, and
  Bilodeau and Brenner carry the Wishart, Hotelling, Wilks, and
  principal-component limits and discriminant analysis. Lauritzen carries
  graphical models. Mardia and Jupp carry the von Mises–Fisher likelihood.
  Anderson and Muirhead also carry correlation theory, covariance tests, and
  factor analysis.
- **[105B](#synopsis-105b)**: Silvey, Pukelsheim, and Fedorov and Hackl carry
  optimal design. Cox and Reid, Bailey, and Cheng carry randomization and
  block designs. Hedayat, Sloane, and Stufken carry orthogonal arrays. Cheng
  carries Latin squares, regular fractions, and resolution. Cochran and
  Särndal, Swensson, and Wretman carry finite-population sampling,
  inclusion-probability estimation, and allocation. Rosenbaum carries
  randomization inference and sensitivity analysis. Pearl carries directed
  interventions, the do-calculus, structural counterfactuals, and
  probabilities of causation. Imbens and Rubin, and Ding, carry potential
  outcomes, completely randomized, stratified, and paired experiments,
  regression adjustment, and instrumental variables; Ding also carries the
  E-value and the mediation formula. Hernán and Robins carry the $g$-formula,
  marginal structural models, and time-varying treatments. Peters, Janzing,
  and Schölkopf carry the graphical and structural-equation account, including
  the identifiability of restricted structural equation models. Spirtes,
  Glymour, and Scheines carry conditional-independence search. The efficiency
  theory used by the doubly robust estimator is in SYNOPSIS102.

### Source comparisons and local copies

#### Survey sampling

Items 72 and 73 describe the finite-population sampling core represented in
Cochran, *Sampling Techniques*, and Särndal, Swensson, and Wretman,
*Model Assisted Survey Sampling*. Neither full text was located in the
local reference directories; the supplemental Ghosh–Meeden file is a
preview and is not treated as a full source. The publisher records were
checked for these two books. Horvitz and Thompson's original paper
is [JASA 47 (1952), 663–685](https://doi.org/10.1080/01621459.1952.10483446).
The formulas were checked directly by finite indicator-moment and
covariance calculations, including the zero row sums for fixed-size
designs, the finite-population correction, and the Cauchy–Schwarz
allocation argument. Positive first-order inclusion suffices for the
total; the displayed unbiased variance estimators additionally require
positive pairwise inclusion. Sample-variance estimation requires at least
two observations in each sampled stratum. These results concern fixed
population values with randomness from the sampling design.

#### Linear models, multivariate analysis, and design

Seber–Lee's Section 3.10 supplies generalized
least squares and Section 10.1 supplies case deletion and studentization;
its Chapters 4 and 12 supply the nested-model and shrinkage framework.
Anderson's Chapters 3, 11, and 12 cover normal covariance likelihood,
principal components, and canonical correlations. The partial-regression,
ridge, and balanced-block formulas are given with their matrix and rank
conditions. Item 40 imposes the sum-of-orders condition on effect
columns; strength $t$ alone does not decorrelate all effects of orders
less than $t$.

The following passages support the numbered statements. Rao's
Section 3b.4 and its Complement 1.5 (Fisher–Cochran and Craig–Sakamoto),
Seber–Lee's Theorems 2.7–2.9 and corollary, and Searle, Casella, and
McCulloch's display (59) and (62) give item 15. Scheffé's Section 2.10,
Theorems 1–3, gives item 16, and his Section 4.3, Tables 4.3.2–4.3.3,
gives item 17. Searle, Casella, and McCulloch's Section 3.5, displays
(60)–(63) and (74), with the comparison of ML, REML, and ANOVA
estimators at (146), gives item 18. Seber–Lee's Section 12.3.2, (12.17)–(12.19),
gives item 19. McCullagh and Nelder's Sections 2.3 and 2.5, and Davison's
Section 10.3.2 on chi-squared approximations for deviances, give items 20 and 21. Muirhead's Theorems 3.2.1, 3.2.5, 3.2.10, 3.2.14, and 3.2.15
give item 31; his Theorems 5.1.1, 5.1.6, and 5.1.7, with Anderson's
Theorems 4.3.5 and 4.4.2, give item 32; his Theorems 8.3.2, 8.3.7,
11.2.1, and 11.2.5, with Anderson's Section 9.4 for Box's multiplier,
give item 33. Anderson's Theorem 8.4.1 and Section 8.5 give the beta
product and the Bartlett expansion of item 23. Anderson's Section 8.6,
Theorem 8.6.1 and Corollary 8.6.1, gives item 34, and his Sections
14.2–14.3, with Theorems 14.3.1 and 14.3.2 and the likelihood-ratio test
of Section 14.3.2, give item 35. The nonsingularity of $(\theta_{ij}^2)$
is the hypothesis of Anderson's Theorem 14.3.2 (after Anderson and Rubin,
1956) for asymptotic normality of the estimators; Anderson states the
chi-squared limit of the likelihood-ratio criterion, his (24), under "the
regularity conditions for $\hat\Psi$ and $\hat\Lambda$ to be
asymptotically normally distributed", which item 35 takes to be those of
Theorem 14.3.2 together with Gaussian sampling.
Lauritzen's Proposition 3.19, Theorem 5.3, Theorem 5.4, and
Proposition 5.9 give item 36. Bailey's Theorem 11.2, Cheng's Exercise
2.5, and Pukelsheim's Section 14.9 give item 42; the trace bound and the
eigenvalue comparison are elementary. Pukelsheim's Section 9.5 gives
item 43. Cheng's Section 8.6 with Theorem 8.10, Bailey's Section 9.2, Cox
and Reid's Section 5.6 on fractional replication, and Cheng's Theorem 9.5
give items 44 and 45.

The local Agresti copies of *Foundations of Linear and Generalized Linear
Models* and *Categorical Data Analysis* are image scans without usable
text extraction. They were not used as full-text evidence;
the linear-model statements use Seber–Lee and Anderson, and the canonical
likelihood calculation specializes the exponential-family formulas in
SYNOPSIS101.

Item 5 is Koenker's Theorem 4.1 (Section 4.2) under his Conditions A1
and A2, checked against the text: A1 asks for absolutely continuous
$F_i$ with continuous densities uniformly bounded away from $0$ and
$\infty$ at the quantiles $\xi_i(\tau)$, and A2 is the three limit
conditions of item 5. Item 5 strengthens the continuity in A1 to
equicontinuity at the quantiles.
Item 22 uses the sample covariance with divisor $n-1$, so that $(n-1)S$ is
Wishart on $n-1$ degrees of freedom. Item 24 uses the divisor $n$; the two
normalizations differ by
$o_P(n^{-1/2})$ for a fixed eigenvalue. Item 37 is the equivalence theorem
for $D$-optimality, together with the general equivalence theorem for concave
Loewner-isotone criteria.

Shape analysis in the sense of Kendall and of Dryden and Mardia is recorded
in [SYNOPSIS108](SYNOPSIS108.md), item 6. Diaconis and Wijsman develop the
group-invariance theory behind the sampling laws of this section; the
numbered entries record the sampling consequences.

#### Causal inference

Ding's Section 18.2 supplies sharp worst-case
bounds and Section 20.2.2, Theorem 20.2, supplies identification at a regression
discontinuity. Item 59 records the elementary two-period identification
identity under an explicit parallel-trends assumption. The variance in
item 56 is obtained from the efficient influence function by conditioning
on $X$. Items 49 and 56 use the sample-splitting conditions in SYNOPSIS102, item 39, when fitted nuisances are evaluated on the observations.

The path-blocking definition and the covariate-kernel $g$-formula specify
that an active path can contain noncolliders outside
the conditioning set, and treatment fixing in a longitudinal intervention
changes which covariate transition laws are integrated. A sharp-null
randomization test is item 38; its exactness does not extend
automatically to the weaker hypothesis of zero average treatment effect.

Item 46 is Ding's Theorem 4.1, including the divisor $n-1$ in $S^2$ and the
identity $\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)=S^2(\tau)/n$.
Item 64 is Pearl's Theorem 3.4.1. The completeness of the rules for
unconditional queries is Huang and Valtorta, "Pearl's calculus of
intervention is complete", UAI 2006, 217–224 (arXiv:1206.6831), Theorem 2,
for causal Bayesian networks with arbitrary unobserved vertices and with
identifiability over models with a common positive observed law (their
Definition 1); for conditional queries in semi-Markovian graphs it is
Shpitser and Pearl, "Identification of conditional interventional
distributions", UAI 2006 (arXiv:1206.6876), Theorem 9, whose Definition 2
quantifies over all causal models inducing $G$ without a positivity
assumption, requiring only $P(z\mid\mathop{\mathrm{do}}(x))>0$. Both
papers were read. Item 49 records the product condition
$o_P(n^{-1/2})$ under which the estimated influence function is efficient.
Item 66 is the paired sensitivity model: the worst-case assignment
probability within a pair is $\Gamma/(1+\Gamma)$.

Further source passages are as follows. Ding: Section
5.3 (stratified experiments, including the comparison (5.4) with complete
randomization) for item 51, where the exact variance difference replaces
Ding's large-stratum approximation and was checked by direct algebra;
Section 7.3 and Theorem 7.1 for item 52;
Section 6.2.2 and Proposition 6.2 for item 53, where the asymptotic
statements were checked against Lin, "Agnostic notes on regression
adjustments to experimental data: reexamining Freedman's critique",
*Ann. Appl. Stat.* 7 (2013), 295–318 (arXiv:1208.2301): Conditions 1–3
of his Section 4.2.1 (bounded finite-population fourth moments of the
potential outcomes and covariates; convergence of $n^{-1}Z^\top Z$, with
$Z$ the matrix of rows $(1,x_i^\top)$, to an invertible limit and of the
population means of the outcomes, their squares and cross products, and
their products with the covariates; $n_1/n\to e\in(0,1)$), Theorem 1
for the limit of $\hat\tau_L$, Corollaries 1.1 and 1.2 for the
comparisons with the unadjusted and Fisher-adjusted estimators (whose
normal limits are Freedman's, 2008), and Theorem 2 for the
conservative Eicker–Huber–White sandwich
$(X^\top X)^{-1}X^\top\mathop{\mathrm{diag}}(\hat\varepsilon_i^2)X(X^\top X)^{-1}$;
Section 13.1,
Theorem 13.1, for item 54;
Sections 23.4–23.6 and Theorem 23.1 for item 55; Theorem 17.1, Lemma 17.1,
and Definition 17.1 for item 60; Definition 27.1, Assumptions 27.2–27.5,
Theorem 27.1, and Example 27.4 for item 61; Problems 29.6–29.8, Theorems
29.6–29.8, for item 69. Pearl: Definitions 7.1.1–7.1.5 for structural
causal models, and Definitions 9.2.1–9.2.3, 9.2.9, 9.2.13 with Theorems
9.2.10, 9.2.11, 9.2.14, and 9.2.15 for item 68. Hernán and Robins,
Sections 12.3–12.4 and 21.2, for stabilized weights and marginal
structural models. Peters, Janzing, and Schölkopf: Lemma 7.8 and Section
7.2.1 for item 70, and Proposition 7.5 and Theorems 7.6–7.7 for item 71.
Item 70 records the population (oracle) form of the PC algorithm; the
sample consistency result of Kalisch and Bühlmann (2007) needs conditions
that are not restated here. Matching-estimator rate theory (Abadie and
Imbens) is outside the selection: Ding's Chapter 15 gives the
bias-corrected estimator but not the rate theory, and the original papers
are not local.

Spirtes, Glymour, and Scheines, *Causation, Prediction, and Search*, and
van der Laan and Rose, *Targeted Learning*, are not in the local reference
directory. The local Rosenbaum file is the 2025 introduction; the 2002
monograph *Observational Studies* is not that file. Tsiatis,
*Semiparametric Theory and Missing Data*, is absent, as already recorded
in the reference guide of SYNOPSIS102.

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
- [Ding, *A First Course in Causal Inference*](../lean-CKMA/References/Ding2024FirstCourseCausalInference-ChapmanHallCRC.TextsStatSci.pdf).
  Theorem 4.1 and the passages listed above were read.
- [Pearl, *Causality*](../lean-CKMA/References/Pearl2009CausalityModelsReasoningInference2ndEd-Cambridge.pdf).
  Theorem 3.4.1 and the Chapter 7 and 9 passages listed above were read.
- [Imbens and Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*](../lean-CKMA/References/ImbensRubin2015CausalInferenceStatisticsSocialBiomedicalSciencesIntroduction-Cambridge.pdf).
- [Hernán and Robins, *Causal Inference: What If*](../lean-CKMA/References/HernánRobins2020CausalInferenceWhatIf-ChapmanHallCRC.pdf).
- [Peters, Janzing, and Schölkopf, *Elements of Causal Inference*](../lean-CKMA/References/PetersJanzingSchölkopf2017ElementsCausalInferenceFoundationsLearningAlgorithms-MITPressAdaptiveCompMl.pdf).
- [Rosenbaum, *An Introduction to the Theory of Observational Studies*](../lean-CKMA/References/Rosenbaum2025IntroductionTheoryObservationalStudies-Springer.STS.pdf).
