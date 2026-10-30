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
