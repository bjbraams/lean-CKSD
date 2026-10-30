# Synopsis: Linear models, multivariate analysis, and experimental design

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-106).

This synopsis follows Section 106. Subdivision 106A is the linear model,
generalised linear models, quantiles, and finite mixtures. Subdivision 106B
is classical multivariate analysis, graphical models, and directional data.
Subdivision 106C is experimental design. Simultaneous confidence procedures
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

## Reference guide

### Correspondence with the subdivisions

- **[106A](#synopsis-106a)**: Rao, Scheffé, Seber and Lee, and Christensen
  carry the linear model. McCullagh and Nelder carry generalised linear
  models and quasi-likelihood. Koenker carries quantile regression.
  McLachlan and Peel carry finite mixtures. Searle, Casella, and McCulloch
  carry residual maximum likelihood in the linear model.
- **[106B](#synopsis-106b)**: Anderson, Muirhead, Mardia, Kent, and Bibby,
  Eaton, and Bilodeau and Brenner carry the Wishart, Hotelling, Wilks, and
  principal-component limits and discriminant analysis. Lauritzen carries
  graphical models. Mardia and Jupp carry the von Mises–Fisher likelihood.
- **[106C](#synopsis-106c)**: Silvey, Pukelsheim, and Fedorov and Hackl carry
  optimal design. Cox and Reid, Bailey, and Cheng carry randomization and
  block designs. Hedayat, Sloane, and Stufken carry orthogonal arrays.

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
- [Lauritzen, *Graphical Models*](../lean-CKMA/References/Lauritzen1996GraphicalModels-Oxford.StatSci17.pdf).
- [Mardia and Jupp, *Directional Statistics*](../lean-CKMA/References/MardiaJupp2000DirectionalStatistics-Wiley.SerProbStat.pdf).
- [Silvey, *Optimal Design*](../lean-CKMA/References/Silvey1980OptimalDesignIntroductionTheoryParameterEstimation-ChapmanHallMonogAPS.pdf).
- [Pukelsheim, *Optimal Design of Experiments*](../lean-CKMA/References/Pukelsheim2006OptimalDesignExperiments-SIAM.CAM50.pdf).
- [Fedorov and Hackl, *Model-Oriented Design of Experiments*](../lean-CKMA/References/FedorovHackl2025ModelOrientedDesignExperiments2ndEd-Springer.LNS209.pdf).
- [Cox and Reid, *The Theory of the Design of Experiments*](../lean-CKMA/References/CoxReid2000TheoryDesignExperiments-ChapmanHallCRC.MSAP86.pdf).
- [Bailey, *Design of Comparative Experiments*](../lean-CKMA/References/Bailey2008DesignComparativeExperiments-Cambridge.SerStatProbMath.pdf).
- [Cheng, *Theory of Factorial Design*](../lean-CKMA/References/Cheng2014TheoryFactorialDesignSingleMultiStratumExperiments-ChapmanHallCRC.MSAP131.pdf).
- [Hedayat, Sloane, and Stufken, *Orthogonal Arrays*](../lean-CKMA/References/HedayatSloaneStufken1999OrthogonalArraysTheoryApplications-Springer.SSS.pdf).
