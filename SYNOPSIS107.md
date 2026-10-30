# Synopsis: High-dimensional statistics and statistical learning

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-107).

This synopsis follows Section 107. Subdivision 107A is sparsity, model
selection, multiple testing, and high-dimensional covariance. Subdivision
107B is uniform convergence, kernels, online prediction, and conformal
prediction. Soft thresholding is [SYNOPSIS104](SYNOPSIS104.md), item 10.
The Sauer–Shelah bound, uniform deviations for VC classes, covariance
estimation, the restricted isometry property, the Marchenko–Pastur law, and
the Tracy–Widom law of the Gaussian unitary ensemble are
[CKMA SYNOPSIS07](../lean-CKMA/SYNOPSIS07.md), items 35, 37, 46, 48, 51, and
69. The representer theorem is SYNOPSIS104, item 8. Bonferroni's method is
[SYNOPSIS102](SYNOPSIS102.md), item 15.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-107a"></a>

## 107A. High-Dimensional and Large-Scale Inference

In the Gaussian sequence model, one observes $Y=\theta+\sigma\xi$ in
$\mathbb R^p$, with $\xi$ standard normal.

* **1. Sparse minimax rate.** Over the class of vectors with at most $s$
  nonzero coordinates, $1\le s\le p/2$, the minimax mean squared error is of
  order $\sigma^2 s\log(p/s)$. When $s$ is known, soft thresholding
  at a level of order $\sigma\sqrt{\log(p/s)}$ attains this order.
  The universal threshold $\sigma\sqrt{2\log p}$ instead gives the
  bound of order $\sigma^2s\log p$ from SYNOPSIS104, item 10; it is
  rate optimal when $\log(p/s)$ is comparable to $\log p$.

Let $Y=X\beta+\varepsilon$ with $X$ an $n\times p$ design and with
$\varepsilon\in\mathbb R^n$. The **lasso** is any minimizer
$$\hat\beta\in\mathop{\mathrm{argmin}}_{\beta\in\mathbb R^p}
\Bigl(\frac1{2n}\|Y-X\beta\|_2^2+\lambda\|\beta\|_1\Bigr).$$
For an index set $S$ and a stretching factor $L>0$, the **compatibility
constant** is
$$\kappa^2(S,L)=\inf\Bigl\{
\frac{|S|\,\|X\delta\|_2^2}{n\|\delta_S\|_1^2}:
\delta\neq0,\;\|\delta_{S^c}\|_1\le L\|\delta_S\|_1\Bigr\}.$$

* **2. Lasso under compatibility.** Suppose $\beta$ is supported on $S$ and
  $$\lambda\ge\frac2n\|X^\top\varepsilon\|_\infty.$$
  If $\kappa(S,3)>0$, then every lasso solution satisfies
  $$\frac1n\|X(\hat\beta-\beta)\|_2^2
  \le\frac{9\lambda^2|S|}{4\kappa^2(S,3)}$$
  and
  $$\|\hat\beta-\beta\|_1\le\frac{6\lambda|S|}{\kappa^2(S,3)}.$$
  The error $\hat\beta-\beta$ lies in the cone
  $\|\delta_{S^c}\|_1\le3\|\delta_S\|_1$. A restricted-eigenvalue lower bound
  on $\|X\delta\|_2/(\sqrt n\,\|\delta\|_2)$ over that cone gives an $\ell^2$
  estimation bound of order $\lambda\sqrt{|S|}$. For a design with
  independent centered sub-Gaussian entries, the restricted isometry property
  of CKMA SYNOPSIS07, item 48, supplies such a bound with high probability
  once $n$ is at least a constant multiple of $|S|\log(ep/|S|)$. If the
  columns satisfy $\|X_{\cdot j}\|_2^2/n\le1$ and the errors are
  $N(0,\sigma^2)$, a choice of $\lambda$ of order $\sigma\sqrt{(\log p)/n}$
  meets the noise condition with high probability.

Let $(S_m)$ be a countable collection of linear subspaces of the regression
space, of dimensions $d_m$, and let $\hat f_m$ be the orthogonal projection
of $Y$ onto $S_m$. Write $\|\cdot\|_n$ for the norm
$\|v\|_n^2=n^{-1}\|v\|_2^2$.

* **3. Penalized model selection.** In the Gaussian regression model with
  error variance $\sigma^2$, let $(\pi_m)$ be positive weights with
  $\sum_m\pi_m\le1$. For a sufficiently large universal constant
  $\kappa$, take
  $$\mathop{\mathrm{pen}}(m)\ge\kappa\frac{\sigma^2}n\bigl(d_m+\log(1/\pi_m)\bigr).$$
  The penalized selector $\hat m$ minimizing
  $\|Y-\hat f_m\|_n^2+\mathop{\mathrm{pen}}(m)$ obeys
  $$\mathbb E\|\hat f_{\hat m}-f\|_n^2
  \le C(\kappa)\inf_m\Bigl(
  \inf_{g\in S_m}\|g-f\|_n^2+\mathop{\mathrm{pen}}(m)\Bigr),$$
  where the constant $C(\kappa)$ depends only on $\kappa$.

* **4. AIC and BIC.** In a regular parametric model of dimension $k$ that
  contains the true distribution, compare the maximized training
  log-likelihood with the log-likelihood of an independent sample of the
  same size, evaluated at the training estimate. Under the regularity and
  moment conditions for taking expectations of the likelihood expansion,
  the expected training excess is $k+o(1)$.
  Akaike's criterion $-2\ell_n(\hat\theta)+2k$ corrects
  the maximized log-likelihood by this optimism. In a finite nested list of
  regular models of fixed dimension, one of which is the smallest model
  containing the truth, the probability that the Akaike selector returns a
  strictly larger model stays positive as $n\to\infty$. The Bayes information
  criterion of SYNOPSIS105, item 5, $-2\ell_n(\hat\theta)+k\log n$, selects
  that smallest true model with probability tending to one.

Let $p_{(1)}\le\cdots\le p_{(m)}$ be ordered $p$-values for $m$ hypotheses,
of which $m_0$ are true nulls, each with a valid $p$-value, and let $V$ and $R$ be the numbers of false
and of all rejections.

* **5. Benjamini–Hochberg procedure.** Fix $\alpha\in(0,1)$ and let
  $k=\max\{i:p_{(i)}\le i\alpha/m\}$, with $k=0$ when the set is empty. Reject
  the hypotheses attached to $p_{(1)},\ldots,p_{(k)}$. If the null $p$-values
  are independent of each other and of the non-null $p$-values, or if the
  vector of $p$-values is positively regression dependent on the subset of
  null coordinates, then the false-discovery rate satisfies
  $$\mathbb E\Bigl[\frac{V}{\max(R,1)}\Bigr]\le\alpha\frac{m_0}m\le\alpha.$$

Let $X$ be an $n\times p$ matrix with independent standard normal entries, and
let $\ell_{\max}$ be the largest eigenvalue of the sample covariance
$n^{-1}X^\top X$. Write $y$ for a limit of $p/n$ in $(0,\infty)$.

* **6. Tracy–Widom law and spiked covariance.** As $n,p\to\infty$ with
  $p/n\to y$,
  $$\frac{\ell_{\max}-\mu_{n,p}}{\sigma_{n,p}}\Rightarrow F_1,$$
  where $F_1$ is the Tracy–Widom law of the Gaussian orthogonal ensemble,
  $$\mu_{n,p}=\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)^2}n,$$
  and
  $$\sigma_{n,p}
  =\frac{\bigl(\sqrt{n-1}+\sqrt p\bigr)
  \bigl((n-1)^{-1/2}+p^{-1/2}\bigr)^{1/3}}n.$$
  The bulk of the spectrum converges to the Marchenko–Pastur law on
  $[(1-\sqrt y)^2,(1+\sqrt y)^2]$, by CKMA SYNOPSIS07, item 51. The edge law
  $F_2$ of the Gaussian unitary ensemble is CKMA SYNOPSIS07, item 69. In
  Johnstone's spiked model, the population covariance has one eigenvalue
  $\alpha$ and the remaining eigenvalues equal to $1$. The corresponding
  sample eigenvalue converges almost surely to $(1+\sqrt y)^2$ when
  $1<\alpha\le1+\sqrt y$, and to $\alpha+y\alpha/(\alpha-1)$ when
  $\alpha>1+\sqrt y$.

### Lower bounds, regularization, and multiplicity

* **14. Le Cam's two-point method.** If two parameters are at metric
  distance at least $2s$, then every estimator satisfies
  $$\max_{j=0,1}P_j(d(\hat\theta,\theta_j)\ge s)
  \ge\tfrac12(1-\|P_0-P_1\|_{\mathrm{TV}}).$$
  For any nonnegative increasing loss $\ell$, this gives a minimax risk
  lower bound $\ell(s)(1-\|P_0-P_1\|_{\mathrm{TV}})/2$.
  The probabilities here are the full observation laws; for $n$
  independent observations the KL divergence used to bound total
  variation is $n$ times the one-observation divergence.

* **15. Fano's method.** Let $\theta_1,\ldots,\theta_M$ be $2s$-separated,
  $M\ge2$, with observation laws $P_j$. For a uniform index $J$ and
  data $X\mid J=j\sim P_j$, every estimator satisfies
  $$\sup_jP_j(d(\hat\theta,\theta_j)\ge s)
  \ge1-\frac{I(J;X)+\log2}{\log M}.$$
  With $\bar P=M^{-1}\sum_jP_j$,
  $$I(J;X)=\frac1M\sum_jD(P_j\|\bar P)
  \le\frac1M\sum_jD(P_j\|Q)$$
  for any reference law $Q$ for which the right side is finite.
  Large packings with small divergences yield the sparse rate of item 1
  and the nonparametric rates in SYNOPSIS104, item 26.

* **16. Lasso without a restricted eigenvalue.** Under the noise event
  of item 2, the basic inequality gives
  $$\frac1n\|X(\hat\beta-\beta)\|^2\le3\lambda\|\beta\|_1.$$
  This prediction bound does not require sparsity or compatibility.
  Compatibility converts the basic inequality into the faster
  $s\lambda^2$ rate of item 2. Small prediction error alone need not
  imply small coefficient error when the design has nearly dependent
  columns.

* **17. Orthogonal designs and soft thresholding.** If
  $X^\top X/n=I_p$, the lasso solution is
  $$\hat\beta_j=\mathop{\mathrm{sign}}(z_j)(|z_j|-\lambda)_+,
  \qquad z=X^\top Y/n.$$
  Ridge instead multiplies $z$ by $n/(n+\lambda)$ for the penalty
  convention of SYNOPSIS106, item 22. The coordinate calculation connects
  sparse regression to Gaussian sequence estimation; correlated designs
  require the cone conditions in item 2.

* **18. Debiased linear estimation.** In the Gaussian linear model let
  $\hat\Theta$ depend on $X$ and define
  $$\tilde\beta=\hat\beta+
  \hat\Theta X^\top(Y-X\hat\beta)/n.$$
  Then the exact decomposition is
  $$\sqrt n(\tilde\beta-\beta)
  =\hat\Theta X^\top\varepsilon/\sqrt n
  +\sqrt n(I-\hat\Theta\hat\Sigma)(\hat\beta-\beta),
  \qquad\hat\Sigma=X^\top X/n.$$
  If $\|\hat\Theta\hat\Sigma-I\|_{\max}
  \|\hat\beta-\beta\|_1=o_P(n^{-1/2})$, each remainder coordinate
  vanishes. Conditionally on $X$, the leading term is Gaussian with
  covariance $\sigma^2\hat\Theta\hat\Sigma\hat\Theta^\top$.
  Consistent variance estimates and variances bounded away from zero
  yield asymptotic coordinate confidence intervals. Suitable sparse
  designs often reduce the remainder condition to $s\log p=o(\sqrt n)$.

* **19. False-discovery control under arbitrary dependence.** Let
  $H_m=\sum_{j=1}^m1/j$. Replacing the Benjamini–Hochberg thresholds in
  item 5 by $i\alpha/(mH_m)$ controls the false-discovery rate at most
  $\alpha m_0/m$ for any joint distribution of valid null $p$-values.
  This is the Benjamini–Yekutieli correction. Family-wise error control
  under arbitrary dependence is SYNOPSIS102, items 23 and 24.

<a id="synopsis-107b"></a>

## 107B. Statistical Learning Theory

Let $(X,Y),(X_1,Y_1),\ldots$ be independent and identically distributed, and
let $\mathcal F$ be a class of measurable decision functions. Write
$R(f)=\mathbb E[L(Y,f(X))]$ and
$R_n(f)=n^{-1}\sum_{i=1}^n L(Y_i,f(X_i))$ for a loss $L$ bounded in $[0,1]$.
The **VC dimension** of a class of binary classifiers is the largest number of
points that the class can shatter, as in CKMA SYNOPSIS07, item 35.

* **7. Fundamental theorem of statistical learning.** For binary
  classification under $0$–$1$ loss, the following are equivalent: the VC
  dimension $v$ is finite; the class is PAC learnable in the realizable case;
  the class is agnostic PAC learnable. In the agnostic case the sample size
  sufficient and necessary for excess risk at most $\varepsilon$, with
  probability at least $1-\delta$, is of order
  $(v+\log(1/\delta))/\varepsilon^2$. In the realizable case the
  corresponding sample size is of order $(v+\log(1/\delta))/\varepsilon$.
  For an empirical-risk minimizer $\hat f$ over a class of VC dimension $v$,
  there is a universal constant $C$ such that, with probability at least
  $1-\delta$,
  $$R(\hat f)\le R_n(\hat f)
  +C\sqrt{\frac{v\log n+\log(1/\delta)}n}.$$
  The uniform deviation behind this bound is CKMA SYNOPSIS07, item 37.

The **empirical Rademacher complexity** of a class $\mathcal F$ on a sample
$x_1,\ldots,x_n$ is
$$\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
=\mathbb E_\sigma\Bigl[\sup_{f\in\mathcal F}
n^{-1}\sum_{i=1}^n\sigma_i f(x_i)\Bigr],$$
where the $\sigma_i$ are independent Rademacher signs.

* **8. Rademacher bound.** For a class of functions with values in $[0,1]$,
  $$\mathbb E\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F).$$
  With probability at least $1-\delta$,
  $$\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\,\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
  +\sqrt{\frac{\log(2/\delta)}{2n}}.$$
  The same bound holds with the empirical complexity in place of its
  expectation, after adding a second term of order
  $\sqrt{\log(1/\delta)/n}$ that comes from the bounded-difference inequality
  for $\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)$.

* **9. Rademacher complexity of a kernel ball.** Let $K$ be a positive
  definite kernel and let $\mathcal H$ be its reproducing-kernel Hilbert
  space. On the ball $\|f\|_{\mathcal H}\le B$,
  $$\widehat{\mathop{\mathrm{Rad}}}_n(\{f:\|f\|_{\mathcal H}\le B\})
  \le\frac Bn\sqrt{\sum_{i=1}^n K(x_i,x_i)}.$$
  A minimizer of empirical risk plus $\lambda\|f\|_{\mathcal H}^2$ has the
  finite expansion of SYNOPSIS104, item 8.

Consider sequential decisions against a sequence of convex losses
$\ell_t:\mathcal Z\to\mathbb R$, chosen by an adversary who may see the past
predictions. The **regret** after $T$ rounds relative to a comparison class
is the excess cumulative loss over the best fixed comparator in hindsight.

* **10. Online gradient descent.** Let the losses be convex and
  $G$-Lipschitz on a convex set of Euclidean diameter $D$. Online gradient
  descent with step size $\eta=D/(G\sqrt T)$ has regret at most $DG\sqrt T$
  against every fixed comparator in the set.

* **11. Hedge.** For $K$ actions and losses with values in $[0,1]$, the
  exponentially weighted forecaster, with learning rate of order
  $\sqrt{(\log K)/T}$, has regret at most $\sqrt{2T\log K}$ against the best
  fixed action.

Split the sample into a training part and a calibration part of size $n$, and
let $s$ be a score trained on the training part. Let
$S_1,\ldots,S_n$ be the calibration scores and let $S_{n+1}=s(X_{n+1},Y_{n+1})$.
Write $S_{(k)}$ for the $k$th smallest calibration score, and set
$S_{(k)}=+\infty$ when $k>n$.

* **12. Split conformal prediction.** Assume that the $n+1$ pairs are
  exchangeable and that the score is a function of the training part and of
  the pair at which it is evaluated. Let
  $k=\lceil(n+1)(1-\alpha)\rceil$ and let $C(x)=\{y:s(x,y)\le S_{(k)}\}$.
  Then
  $$\mathbb P\bigl(Y_{n+1}\in C(X_{n+1})\bigr)\ge1-\alpha.$$
  If the $n+1$ scores are almost surely distinct, the same probability is at
  most $1-\alpha+1/(n+1)$.

* **13. No free lunch.** Let the feature space be infinite. For every $n$,
  every classification rule based on a sample of size $n$, and every
  $\varepsilon>0$, there exists a distribution, with Bayes error equal to
  zero, under which the expected $0$–$1$ error of the rule is at least
  $1/2-\varepsilon$.

### Statistical targets in classification

* **20. Bayes classification risk.** For binary labels and
  $\eta(x)=P(Y=1\mid X=x)$, a risk-minimizing classifier is
  $g^*(x)=1_{\{\eta(x)\ge1/2\}}$. For every measurable classifier $g$,
  $$R(g)-R(g^*)=\mathbb E\bigl[|2\eta(X)-1|
  1_{\{g(X)\ne g^*(X)\}}\bigr].$$
  A plug-in classifier $\hat g=1_{\{\hat\eta\ge1/2\}}$ satisfies
  $R(\hat g)-R(g^*)\le2\mathbb E|\hat\eta(X)-\eta(X)|$, conditionally
  on independent training data. If
  $P(|\eta(X)-1/2|\le t)\le Ct^\alpha$ for all $t>0$ and
  $\|\hat\eta-\eta\|_\infty\le\delta$, the excess risk is at most
  $2C\delta^{\alpha+1}$. This margin assumption explains rates faster
  than a distribution-free risk bound.

* **21. Empirical risk minimization.** If $\hat f$ minimizes empirical risk
  over $\mathcal F$ up to error $\varepsilon_n$, then
  $$R(\hat f)-\inf_{f\in\mathcal F}R(f)
  \le2\sup_{f\in\mathcal F}|R_n(f)-R(f)|+\varepsilon_n.$$
  Thus the uniform deviations of items 7 and 8 control estimation error
  within a class. The difference between $\inf_{f\in\mathcal F}R(f)$ and
  the unrestricted Bayes risk is a separate approximation error.

## Reference guide

### Correspondence with the subdivisions

- **[107A](#synopsis-107a)**: van de Geer, Wainwright, Giraud, Koltchinskii,
  and Massart carry sparsity and penalized model selection. Dudoit and van
  der Laan, and Dickhaus, carry multiple testing. Yao, Zheng, and Bai carry
  the Wishart edge and the spiked model. Vershynin, Boucheron, Lugosi, and
  Massart, Tropp, and Foucart and Rauhut supply the concentration and
  restricted-isometry ingredients cited from the analysis synopsis.
- **[107B](#synopsis-107b)**: Vapnik, Anthony and Bartlett, Mohri,
  Rostamizadeh, and Talwalkar, and Devroye, Györfi, and Lugosi carry VC
  theory and the no-free-lunch theorem. Cesa-Bianchi and Lugosi carry online
  regret. Koltchinskii carries the Rademacher and kernel bounds.

### Source comparisons and local copies

Wainwright's Chapter 15 was read for the estimation-to-testing
reduction, Le Cam's method, and Proposition 15.12 on Fano's method.
Its sparse-regression and model-selection chapters supply the surrounding
regularization framework. Item 1 distinguishes a sparsity-tuned
threshold from the universal threshold, and item 3 requires a sufficiently
large penalty multiplier. Item 18 states the exact bias decomposition
and a sufficient remainder condition, without asserting asymptotic
normality for arbitrary designs. Items 20 and 21 separate Bayes risk,
approximation error, and the uniform deviations already cited from CKMA.

Item 2 is the consequence, at stretching factor $3$, of the sharp oracle
inequality in van de Geer for the lasso normalized as
$n^{-1}\|Y-X\beta\|_2^2+2\lambda\|\beta\|_1$. The factor $3$ is the cone
constant obtained when the penalty level is at least twice
$n^{-1}\|X^\top\varepsilon\|_\infty$. Item 6 follows Yao, Zheng, and Bai:
the centering $\mu_{n,p}$ is asymptotic to the Marchenko–Pastur right edge
$(1+\sqrt y)^2$, and the spike map $\alpha+y\alpha/(\alpha-1)$ is continuous
at the threshold $1+\sqrt y$.

Bühlmann and van de Geer, *Statistics for High-Dimensional Data*, Hastie,
Tibshirani, and Friedman, *The Elements of Statistical Learning*,
Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
Steinwart and Christmann, *Support Vector Machines*,
Vovk, Gammerman, and Shafer, *Algorithmic Learning in a Random World*, and
Efron, *Large-Scale Inference*, are not in the local reference directory.
Item 12 is the split-conformal coverage theorem of that literature. The
false-discovery statement in item 5 is the Benjamini–Hochberg theorem under
independence and under positive regression dependence. A supplemental
copy of Cucker and Zhou, *Learning Theory*, is present but was not read
for this expansion.

Local texts directly consulted or identified for this selection:

- [van de Geer, *Estimation and Testing Under Sparsity*](../lean-CKMA/References/VanDeGeer2016EstimationTestingUnderSparsityÉcoleDÉtéProbabilitésSaintFlourXLV2015-Springer.LNM2159.pdf).
- [Wainwright, *High-Dimensional Statistics*](../lean-CKMA/References/Wainwright2019HighDimensionalStatistics-Cambridge.pdf).
- [Giraud, *Introduction to High-Dimensional Statistics*](../lean-CKMA/References/Giraud2022IntroductionHighDimensionalStatistics2ndEd-ChapmanHallCRC.MSAP168.pdf).
- [Massart, *Concentration Inequalities and Model Selection*](../lean-CKMA/References/Massart2007ConcentrationInequalitiesModelSelectionÉcoleDÉtéProbabilitésSaintFlourXXXIII2003-Springer.LNM1896.pdf).
- [Koltchinskii, *Oracle Inequalities in Empirical Risk Minimization*](../lean-CKMA/References/Koltchinskii2011OracleInequalitiesEmpiricalRiskMinimizationSparseRecoveryProblems-Springer.LNM2033.pdf).
- [Yao, Zheng, and Bai, *Large Sample Covariance Matrices and High-Dimensional Data Analysis*](../lean-CKMA/References/YaoZhengBai2015LargeSampleCovarianceMatricesHighDimensionalDataAnalysis-Cambridge.SerStatProbMath.pdf).
- [Dudoit and van der Laan, *Multiple Testing Procedures*](../lean-CKMA/References/DudoitVanDerLaan2008MultipleTestingProceduresApplicationsGenomics-Springer.SSS.pdf).
- [Dickhaus, *Simultaneous Statistical Inference*](../lean-CKMA/References/Dickhaus2014SimultaneousStatisticalInferenceApplicationsLifeSciences-Springer.pdf).
- [Vershynin, *High-Dimensional Probability*](../lean-CKMA/References/Vershynin2018HighDimensionalProbabilityIntroductionApplicationsDataScience-CambridgeSerStatProbMath47.pdf).
- [Boucheron, Lugosi, and Massart, *Concentration Inequalities*](../lean-CKMA/References/BoucheronLugosiMassart2013ConcentrationInequalitiesNonasymptoticTheoryIndependence-Oxford.pdf).
- [Foucart and Rauhut, *A Mathematical Introduction to Compressive Sensing*](../lean-CKMA/References/FoucartRauhut2013MathematicalIntroductionCompressiveSensing-BirkhäuserANHA.pdf).
- [Vapnik, *Statistical Learning Theory*](../lean-CKMA/References/Vapnik1998StatisticalLearningTheory-WileyInterscience.pdf).
- [Anthony and Bartlett, *Neural Network Learning*](../lean-CKMA/References/AnthonyBartlett1999NeuralNetworkLearningTheoreticalFoundations-Cambridge.pdf).
- [Mohri, Rostamizadeh, and Talwalkar, *Foundations of Machine Learning*](../lean-CKMA/References/MohriRostamizadehTalwalkar2018FoundationsMachineLearning2ndEd-MITPress.ACML.pdf).
- [Devroye, Györfi, and Lugosi, *A Probabilistic Theory of Pattern Recognition*](../lean-CKMA/References/DevroyeGyörfiLugosi1996ProbabilisticTheoryPatternRecognition-Springer.SMAP31.pdf).
- [Cesa-Bianchi and Lugosi, *Prediction, Learning, and Games*](../lean-CKMA/References/CesaBianchiLugosi2006PredictionLearningGames-Cambridge.pdf).
