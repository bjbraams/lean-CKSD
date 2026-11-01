# Synopsis: Causal inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-109).

This synopsis follows Section 109. The objects are potential outcomes and
interventions on directed graphical models, together with the structural
counterfactuals, mediation, sensitivity, and discovery questions they
raise. Missingness at random, the
efficient influence function for a missing mean, and semiparametric
efficiency are [SYNOPSIS104](SYNOPSIS104.md), items 15, 17, and 14.
Undirected Markov properties are SYNOPSIS106, item 12. The Cox model is
[SYNOPSIS108](SYNOPSIS108.md), item 14. Section 109 has no lettered
subdivision in the bibliography.

A unit has **potential outcomes** $Y(a)$ under each treatment level $a$ in
a finite set of treatments. The **stable unit treatment value assumption**
is that these potential outcomes do not depend on the treatments of other
units and that each treatment level has one version. The observed outcome
is the potential outcome of the treatment actually received. For a binary
treatment $A\in\{0,1\}$, the **average treatment effect** is
$\theta=\mathbb E[Y(1)-Y(0)]$.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

## Experiments, identification, and estimation

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

* **1. Neyman's theorem.** In a completely randomized experiment the
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

* **2. Identification by regression and by weighting.** Under conditional
  ignorability and positivity,
  $$\mathbb E[Y(a)]
  =\mathbb E\bigl[m_a(X)\bigr]
  =\mathbb E\Bigl[\frac{1_{\{A=a\}}Y}{e_a(X)}\Bigr].$$
  For a binary treatment the average treatment effect is therefore
  $\mathbb E[m_1(X)-m_0(X)]$.

A measurable function $b$ of $X$ is a **balancing score** when
$A\perp X\mid b(X)$. The **propensity score** of a binary treatment is
$e(X)=P(A=1\mid X)$.

* **3. Propensity score.** Under conditional ignorability, $Y(a)$ is
  independent of $A$ given $e(X)$. The propensity score is a balancing
  score, and it is a function of every balancing score.

Write $\mu_a$ for a candidate regression and $e$ for a candidate propensity
score, and set
$$
\varphi
=\mu_1(X)-\mu_0(X)
+\frac{A\bigl(Y-\mu_1(X)\bigr)}{e(X)}
-\frac{(1-A)\bigl(Y-\mu_0(X)\bigr)}{1-e(X)}.
$$

* **4. Doubly robust estimator of the average treatment effect.** Assume
  conditional ignorability and $e_0(X)\in[\delta,1-\delta]$. The expectation
  of $\varphi$ equals $\theta$ as soon as either $e=e_0$ and the functions
  $\mu_a$ are square-integrable, or $\mu_a=m_a$ for $a\in\{0,1\}$ and $e$
  is any measurable function with values in $[\delta,1-\delta]$. The sample
  average of $\varphi$, with estimated nuisance functions, is therefore
  consistent when at least one of the two fitted models is correct. If both
  are correct and the product of their $L^2$ errors is $o_P(n^{-1/2})$, the
  estimator is asymptotically linear with efficient influence function
  $\varphi-\theta$, provided the empirical-process remainder is controlled,
  for example by cross-fitting and $L^2$ convergence of the fitted
  estimating function as specified in SYNOPSIS104, item 28. The missing-mean analogue is SYNOPSIS104, item 17, and
  the efficiency bound is SYNOPSIS104, item 14.

Let $Z\in\{0,1\}$ be an instrument, let $A(z)$ be the potential treatment,
and let $Y(a)$ be the potential outcome. **Exclusion** means that the
instrument affects the outcome only through $A$. **Monotonicity** means
$A(1)\ge A(0)$ almost surely. A unit is a **complier** when
$A(1)>A(0)$.

* **5. Local average treatment effect.** Assume that
  $(Y(0),Y(1),A(0),A(1))$ is independent of $Z$, that exclusion and
  monotonicity hold, and that $P(A=1\mid Z=1)\ne P(A=1\mid Z=0)$. Then the
  Wald ratio equals the average treatment effect on the compliers:
  $$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
  {\mathbb E[A\mid Z=1]-\mathbb E[A\mid Z=0]}
  =\mathbb E\bigl[Y(1)-Y(0)\mid A(1)>A(0)\bigr].$$

### Stratified, paired, and regression-adjusted experiments

The sharp-null randomization test, valid in each of the designs below, is
SYNOPSIS106, item 15. In a **stratified randomized experiment** the units are
partitioned into strata $k=1,\ldots,K$ of sizes $n_{[k]}$, with
$\pi_{[k]}=n_{[k]}/n$, and independent completely randomized experiments with
$n_{[k]1}$ treated and $n_{[k]0}$ control units are run within the strata.
Write $\tau_{[k]}$, $\hat\tau_{[k]}$, and $S^2_{[k]}(\cdot)$ for the
quantities of item 1 within stratum $k$, and $\bar Y_{[k]}(a)$ for the
stratum mean of $Y(a)$.

* **16. Stratified experiments.** The stratified estimator
  $\hat\tau_S=\sum_k\pi_{[k]}\hat\tau_{[k]}$ is unbiased for $\tau$, with
  $$\mathop{\mathrm{Var}}(\hat\tau_S)=\sum_{k=1}^K\pi_{[k]}^2\Bigl(
  \frac{S^2_{[k]}(1)}{n_{[k]1}}+\frac{S^2_{[k]}(0)}{n_{[k]0}}
  -\frac{S^2_{[k]}(\tau)}{n_{[k]}}\Bigr).$$
  If every arm of every stratum has at least two units, the estimator
  $\hat V_S=\sum_k\pi_{[k]}^2\bigl(\hat S^2_{[k]}(1)/n_{[k]1}
  +\hat S^2_{[k]}(0)/n_{[k]0}\bigr)$ is conservative, exactly as in item 1.
  If the treated fraction $n_{[k]1}/n_{[k]}$ is the same in every stratum,
  then $\hat\tau_S$ equals the difference in means, and for large strata the
  variance under complete randomization exceeds that under stratification by
  approximately
  $$\sum_{k=1}^K\frac{\pi_{[k]}}n\Bigl\{\Bigl(\frac{n_0}{n_1}\Bigr)^{1/2}
  \bigl(\bar Y_{[k]}(1)-\bar Y(1)\bigr)+\Bigl(\frac{n_1}{n_0}\Bigr)^{1/2}
  \bigl(\bar Y_{[k]}(0)-\bar Y(0)\bigr)\Bigr\}^2\ge0.$$
  The gain vanishes only when the stratifying variable does not predict the
  potential outcomes in this sense.

In a **matched-pairs experiment** there are $n$ pairs of units, and within
each pair one unit is assigned to treatment by an independent fair coin. Let
$\tau_i$ be the average of the two unit effects in pair $i$,
$\tau=n^{-1}\sum_i\tau_i$, and let $\hat\tau_i$ be the treated-minus-control
difference in pair $i$, with $\hat\tau=n^{-1}\sum_i\hat\tau_i$.

* **17. Matched-pairs experiments.** The estimator $\hat\tau$ is unbiased for
  $\tau$. Although no within-pair variance can be estimated, the
  between-pair estimator $\hat V=\{n(n-1)\}^{-1}\sum_i(\hat\tau_i-\hat\tau)^2$
  is conservative:
  $$\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)
  =\frac1{n(n-1)}\sum_{i=1}^n(\tau_i-\tau)^2\ge0,$$
  with equality when the pair effects $\tau_i$ are all equal. The estimator
  and its variance estimate coincide with the one-sample $t$ analysis of the
  differences $\hat\tau_i$.

In the completely randomized experiment of item 1, let $x_i$ be fixed
covariate vectors centered so that $\bar x=0$. **Fisher's covariance-adjusted
estimator** $\hat\tau_F$ is the coefficient of the treatment indicator in the
least-squares fit of $Y$ on $(1,A,x)$. **Lin's estimator** $\hat\tau_L$ is the
coefficient of $A$ in the least-squares fit of $Y$ on $(1,A,x,Ax)$.

* **18. Regression adjustment in randomized experiments.** For fixed
  vectors $b_1,b_0$, the adjusted difference in means
  $$\hat\tau(b_1,b_0)=n_1^{-1}\sum_iA_i(Y_i-b_1^\top x_i)
  -n_0^{-1}\sum_i(1-A_i)(Y_i-b_0^\top x_i)$$
  is unbiased for $\tau$, with the variance of item 1 computed from the
  adjusted potential outcomes $Y_i(a)-b_a^\top x_i$. Lin's estimator is
  $\hat\tau(\hat b_1,\hat b_0)$ with $\hat b_a$ the least-squares slope of $Y$
  on $x$ in arm $a$; it equals the difference of the two arm-wise fitted
  intercepts. Under finite-population asymptotics with a fixed number of
  covariates and suitable moment conditions, $\hat\tau_L$ is consistent and
  asymptotically normal, its asymptotic variance is no larger than that of
  the difference in means or of $\hat\tau_F$, and the
  heteroscedasticity-robust (Eicker–Huber–White) standard error is
  conservative. By contrast, $\hat\tau_F$ is biased in finite samples, can be
  less precise than the difference in means when $n_1\ne n_0$, and its usual
  homoscedastic standard error is inconsistent (Freedman). None of these
  conclusions requires the linear model to be correct; the randomization
  alone justifies them.

### Treated-unit effects and instrumental variables

* **19. Average effect on the treated.** For a binary treatment with
  propensity score $e$, suppose only $Y(0)\perp A\mid X$ and $e(X)<1$ almost
  surely. Then the average treatment effect on the treated,
  $\tau_T=\mathbb E[Y(1)-Y(0)\mid A=1]$, is identified by
  $$\tau_T=\mathbb E[Y\mid A=1]-\mathbb E\bigl[m_0(X)\mid A=1\bigr]
  =\mathbb E[Y\mid A=1]-\frac{\mathbb E\bigl[(1-A)\,e(X)Y/(1-e(X))\bigr]}{P(A=1)}.$$
  Only one-sided ignorability and overlap are needed, because the
  counterfactual mean concerns the control outcome of treated units.

In the **linear instrumental-variable model**
$Y=D^\top\beta+\varepsilon$, the regressor vector $D$ may be correlated with
$\varepsilon$, and an instrument vector $Z$ satisfies $\mathbb E[Z\varepsilon]=0$,
with $\mathbb E[ZZ^\top]$ nonsingular and $\mathbb E[ZD^\top]$ of full column
rank. Observed and exogenous regressors are included in both $D$ and $Z$.
The **two-stage least-squares estimator** regresses $D$ on $Z$ by least
squares and then $Y$ on the fitted values $\hat D$.

* **20. Two-stage least squares.** For independent copies with finite second
  moments,
  $$\hat\beta_{\mathrm{tsls}}=\beta+\Bigl(\sum_i\hat D_i\hat D_i^\top\Bigr)^{-1}
  \sum_i\hat D_i\varepsilon_i\to_P\beta.$$
  With finite fourth moments it is asymptotically normal, and a consistent
  sandwich variance estimate uses the residuals $Y_i-\hat\beta^\top_{\mathrm{tsls}}D_i$,
  not the second-stage residuals $Y_i-\hat\beta^\top_{\mathrm{tsls}}\hat D_i$. When
  $D$ and $Z$ have the same dimension, it equals the instrumental-variable
  estimator $(\sum_iZ_iD_i^\top)^{-1}\sum_iZ_iY_i$. With one endogenous
  regressor and one instrument it equals the ratio of the reduced-form
  coefficients of $Z$ for $Y$ and for $D$; for binary $Z$ and $D$ without
  covariates this is the Wald ratio of item 5, which estimates the complier
  effect even when constant linear effects fail. The rank condition is the
  population form of instrument relevance; with weak instruments the normal
  approximation can be poor.

### Efficiency, partial identification, and design-based identification

* **11. Efficient variance for an average treatment effect.** Under the
  assumptions of item 4, write $\sigma_a^2(X)=\mathop{\mathrm{Var}}(Y\mid
  A=a,X)$ and suppose the following expression is finite. In the
  unrestricted observed-data model the efficient influence function is
  $\varphi-\theta$ with true nuisance functions, and its variance is
  $$\mathop{\mathrm{Var}}(m_1(X)-m_0(X))+
  \mathbb E\left[\frac{\sigma_1^2(X)}{e_0(X)}+
  \frac{\sigma_0^2(X)}{1-e_0(X)}\right].$$
  Cross-fitting with the $L^2$ and product-rate conditions of SYNOPSIS104,
  item 28, for each arm yields an estimator attaining this bound.
  Small treatment probabilities increase the information cost of
  estimating the corresponding conditional mean.

* **12. Bounds without ignorability.** Suppose only consistency and
  $0\le Y(a)\le1$. Write $p=P(A=1)\in(0,1)$ and
  $\mu_a=\mathbb E[Y\mid A=a]$. Then the average treatment effect lies in
  $$[p\mu_1-(1-p)\mu_0-p,\quad
  p\mu_1+(1-p)-(1-p)\mu_0].$$
  These bounds are sharp: every value in the interval is compatible with
  the observed law. They result from letting each unobserved potential
  outcome range over $[0,1]$. Additional independence, monotonicity, or
  instrumental-variable restrictions can narrow the interval.

* **13. Regression discontinuity.** Let treatment be
  $A=1_{\{X\ge c\}}$, with observations possible on both sides of $c$.
  If $x\mapsto\mathbb E[Y(a)\mid X=x]$ has a version continuous at $c$
  for each $a$, then the effect at the cutoff is identified by
  $$\mathbb E[Y(1)-Y(0)\mid X=c]
  =\lim_{x\downarrow c}\mathbb E[Y\mid X=x]
  -\lim_{x\uparrow c}\mathbb E[Y\mid X=x].$$
  The conditional effect at a null-probability cutoff is understood
  through these continuous versions. This identifies a local effect even
  though ordinary treatment positivity fails at each running-variable value.

* **14. Difference in differences.** For two periods $t=0,1$ and group
  indicator $G$, suppose only group $G=1$ receives treatment at $t=1$.
  Assume no anticipation, consistency, and parallel untreated mean trends:
  $$\mathbb E[Y_1(0)-Y_0(0)\mid G=1]
  =\mathbb E[Y_1(0)-Y_0(0)\mid G=0].$$
  Then the average effect on the treated at time 1 equals
  $$\{\mathbb E[Y_1\mid G=1]-\mathbb E[Y_0\mid G=1]\}
  -\{\mathbb E[Y_1\mid G=0]-\mathbb E[Y_0\mid G=0]\}.$$
  The group populations must be comparable over time, as with panel data
  or repeated samples from unchanged group populations. Parallel trends
  is a restriction on counterfactual means, not a consequence of an
  observed regression fit.

### Sensitivity to unmeasured confounding and mediation

Let the treatment $A$ and outcome $Y$ be binary, let $U$ be a binary
unmeasured confounder with $A\perp Y\mid(X,U)$, and, at a fixed value $x$ of
the measured covariates, write
$$\mathrm{rr}_{AU}=\frac{P(U=1\mid A=1,x)}{P(U=1\mid A=0,x)},\qquad
\mathrm{rr}_{UY}=\frac{P(Y=1\mid U=1,x)}{P(Y=1\mid U=0,x)},\qquad
\mathrm{rr}^{\mathrm{obs}}=\frac{P(Y=1\mid A=1,x)}{P(Y=1\mid A=0,x)}.$$

* **21. Cornfield inequalities and the E-value.** If
  $\mathrm{rr}^{\mathrm{obs}}>1$, $\mathrm{rr}_{AU}>1$, and
  $\mathrm{rr}_{UY}>1$, then
  $$\mathrm{rr}^{\mathrm{obs}}\le
  \frac{\mathrm{rr}_{AU}\,\mathrm{rr}_{UY}}{\mathrm{rr}_{AU}+\mathrm{rr}_{UY}-1}.$$
  Consequently both $\mathrm{rr}_{AU}$ and $\mathrm{rr}_{UY}$ are at least
  $\mathrm{rr}^{\mathrm{obs}}$ (Cornfield's inequality), and
  $$\max(\mathrm{rr}_{AU},\mathrm{rr}_{UY})\ge
  \mathrm{rr}^{\mathrm{obs}}+\sqrt{\mathrm{rr}^{\mathrm{obs}}
  (\mathrm{rr}^{\mathrm{obs}}-1)}.$$
  The right side is the **E-value** of Ding and VanderWeele: an unmeasured
  confounder that fully explains an observed risk ratio must be associated
  with both treatment and outcome at least this strongly on the risk-ratio
  scale. The case $\mathrm{rr}^{\mathrm{obs}}<1$ follows by relabeling the
  treatment levels. Item 10 is the corresponding design-based sensitivity
  analysis for matched pairs.

For a binary treatment $A$, a mediator $M$, and outcome $Y$, let $M(a)$ be the
potential mediator and $Y(a,m)$ the potential outcome with consistency
$M=M(A)$ and $Y=Y(A,M)$. Write $Y(a,M(a'))$ for the nested potential outcome
and define the **natural direct** and **natural indirect effects**
$$\mathrm{NDE}=\mathbb E\bigl[Y(1,M(0))-Y(0,M(0))\bigr],\qquad
\mathrm{NIE}=\mathbb E\bigl[Y(1,M(1))-Y(1,M(0))\bigr],$$
whose sum is the total effect $\mathbb E[Y(1,M(1))-Y(0,M(0))]$.

* **22. Mediation formula.** Assume, for all $a,a',m$, that
  $A\perp Y(a,m)\mid X$, $M\perp Y(a,m)\mid(X,A)$, $A\perp M(a)\mid X$, and the
  cross-world independence $Y(a,m)\perp M(a')\mid X$, together with
  positivity of the conditioning events. Then, for discrete $M$ and $X$,
  $$\mathbb E\bigl[Y(a,M(a'))\bigr]=\sum_x\sum_m
  \mathbb E[Y\mid A=a,M=m,X=x]\,P(M=m\mid A=a',X=x)\,P(X=x),$$
  with integrals against conditional densities in general. Hence the natural
  direct and indirect effects are identified. The first three conditions
  hold when treatment and mediator are both randomized given $X$; the
  cross-world condition cannot be ensured by any experiment and is not
  testable. In a structural causal model whose treatment, mediator, and
  outcome equations have mutually independent errors and depend on $X$,
  all four conditions hold.

## Graphical interventions

Let $G$ be a directed acyclic graph on a finite set of vertices, and let
the law of the corresponding random vector admit a recursive factorization
along $G$. A path is **blocked** by $W$ if at least one noncollider on
the path belongs to $W$, or at least one collider has no descendant,
including itself, in $W$. Two disjoint vertex sets are **$d$-separated**
by a third if every path between them is blocked. The **global Markov property** says
that $d$-separation implies the corresponding conditional independence.

* **6. Directed Markov properties.** For a directed acyclic graph, recursive
  factorization, the local Markov property, and the global Markov property
  are equivalent for every such factorization. The undirected
  Hammersley–Clifford theorem is SYNOPSIS106, item 12.

For an intervention $\mathop{\mathrm{do}}(X=x)$, write $G_{\bar X}$ for the
graph with arrows into $X$ removed and $G_{\underline Z}$ for the graph
with arrows out of $Z$ removed. A set $Z$ satisfies the **back-door
criterion** relative to $(X,Y)$ when no vertex of $Z$ is a descendant of
$X$ and $Z$ blocks every path from $X$ to $Y$ that contains an arrow into
$X$. A set $Z$ satisfies the **front-door criterion** when $Z$ intercepts
every directed path from $X$ to $Y$, every back-door path from $X$ to $Z$
is blocked, and $X$ blocks every back-door path from $Z$ to $Y$.

* **7. Back-door and front-door formulae.** If $Z$ satisfies the back-door
  criterion relative to $(X,Y)$, then
  $$P\bigl(y\mid\mathop{\mathrm{do}}(x)\bigr)
  =\sum_z P(y\mid x,z)\,P(z).$$
  If $Z$ satisfies the front-door criterion, then
  $$P\bigl(y\mid\mathop{\mathrm{do}}(x)\bigr)
  =\sum_z P(z\mid x)\sum_{x'}P(y\mid x',z)\,P(x').$$

* **8. Rules of the do-calculus.** Let $X,Y,Z,W$ be disjoint sets of
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
  These are Pearl's Theorem 3.4.1. A query
  $P(y\mid\mathop{\mathrm{do}}(x),z)$ is identifiable from the observational
  law if and only if these rules reduce it to an expression that contains
  no intervention.

Let $A_t$ be a treatment at time $t=0,\ldots,T$, let $H_t$ be the history
available just before $A_t$, and let $Y(\bar a)$ be the outcome under a
treatment regime $\bar a=(a_0,\ldots,a_T)$. **Sequential exchangeability**
is the independence
$Y(\bar a)\perp A_t\mid H_t,\,A_{0:t-1}=a_{0:t-1}$ at each $t$.
**Sequential positivity** is a lower bound, uniform in $t$, on the
conditional probability of $A_t=a_t$ given the observed past.

* **9. Longitudinal $g$-formula.** Write
  $H_t=(L_0,A_0,L_1,\ldots,A_{t-1},L_t)$, where $L_0$ is baseline
  and $L_t$ is measured before $A_t$. Under consistency, sequential
  exchangeability, and sequential positivity, for discrete covariates,
  $$\mathbb E[Y(\bar a)]
  =\sum_{\bar l} \mathbb E[Y\mid\bar L_T=\bar l,\bar A_T=\bar a]
  P(L_0=l_0)\prod_{t=1}^T
  P(L_t=l_t\mid\bar L_{t-1}=\bar l_{t-1},
  \bar A_{t-1}=\bar a_{t-1}).$$
  Integrals against the corresponding conditional kernels replace sums
  for general covariates. Successive regression implements this formula
  by setting each treatment to its prescribed value while integrating
  over the covariate transition law under the preceding treatments.

For a matched-pair observational study, Rosenbaum's model with parameter
$\Gamma\ge1$ bounds the ratio of the two units' treatment odds within
each pair between $1/\Gamma$ and $\Gamma$. Conditional on one treated
unit per pair, each assignment probability therefore lies between
$1/(1+\Gamma)$ and $\Gamma/(1+\Gamma)$.

* **10. Sensitivity of a randomization test.** Under that odds constraint,
  the tail probability of a test statistic is maximized by an explicit
  product of biased pair assignments, with success probabilities
  $\Gamma/(1+\Gamma)$ or $1/(1+\Gamma)$ according to the sign that enlarges
  the tail. The resulting upper bound is a valid $p$-value throughout the
  sensitivity model. At $\Gamma=1$ the bound is the randomization $p$-value
  of the paired experiment.

* **15. Markov equivalence of directed graphs.** Two directed acyclic
  graphs have the same $d$-separation relations if and only if they have
  the same skeleton and the same unshielded colliders
  $i\to j\leftarrow k$ with $i,k$ nonadjacent. Under **faithfulness**,
  the conditional independences of the distribution are exactly those
  implied by $d$-separation. Even with faithfulness and unlimited
  observational data, conditional-independence information in general
  determines only this equivalence class. Interventions can distinguish
  members because they change the factorization in different ways.

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

* **23. Probabilities of causation.** Under exogeneity,
  $$\max\bigl\{0,P(y\mid x)-P(y\mid x')\bigr\}\le\mathrm{PNS}\le
  \min\bigl\{P(y\mid x),P(y'\mid x')\bigr\},$$
  both bounds are sharp, and
  $\mathrm{PN}=\mathrm{PNS}/P(y\mid x)$ and $\mathrm{PS}=\mathrm{PNS}/P(y'\mid x')$.
  If in addition $Y$ is monotone in $X$, all three are identified, with
  $\mathrm{PNS}=P(y\mid x)-P(y\mid x')$ and the excess risk ratio
  $$\mathrm{PN}=\frac{P(y\mid x)-P(y\mid x')}{P(y\mid x)}.$$
  Under monotonicity alone, whenever $P(y_x)$ and $P(y_{x'})$ are identified,
  $\mathrm{PNS}=P(y_x)-P(y_{x'})$, $\mathrm{PN}=(P(y)-P(y_{x'}))/P(x,y)$,
  and $\mathrm{PS}=(P(y_x)-P(y))/P(x',y')$. These are unit-level
  counterfactual quantities: unlike average effects, they are not identified
  by randomization without monotonicity.

In the setting of item 9, write
$e_t(a_t\mid H_t,\bar a_{t-1})=P(A_t=a_t\mid H_t,A_{0:t-1}=\bar a_{t-1})$ for
the treatment probabilities. A **marginal structural model** is a
parametric model $\mathbb E[Y(\bar a)\mid L_0]=f(\bar a,L_0;\beta)$ for the
regime-specific means.

* **24. Inverse probability weighting for time-varying treatments.**
  Under consistency, sequential exchangeability, and sequential positivity,
  $$\mathbb E[Y(\bar a)]=\mathbb E\Bigl[\frac{1_{\{\bar A_T=\bar a\}}\,Y}
  {\prod_{t=0}^Te_t(a_t\mid H_t,\bar a_{t-1})}\Bigr],$$
  which equals the $g$-formula of item 9. If the marginal structural model
  is correct, its parameter is the minimizer
  $$\beta=\mathop{\mathrm{arg\,min}}_b\sum_{\bar a}\mathbb E\Bigl[
  \frac{1_{\{\bar A_T=\bar a\}}}{\prod_te_t(a_t\mid H_t,\bar a_{t-1})}
  \bigl(Y-f(\bar a,L_0;b)\bigr)^2\Bigr],$$
  so it is estimated by weighted least squares with estimated treatment
  probabilities. Multiplying the weights by a function of $(\bar a,L_0)$,
  such as the product of the marginal treatment probabilities, gives
  **stabilized weights** without changing the limit when $f$ is correct. Time-varying
  confounders affected by earlier treatment are handled here, whereas
  ordinary regression adjustment for them can be biased.

### Causal discovery

* **25. Skeleton and colliders from conditional independences.** In a
  directed acyclic graph, two vertices are adjacent if and only if no subset
  of the other vertices $d$-separates them, and two nonadjacent vertices are
  $d$-separated by the parents of one of them. If $i-j-k$ is a path in the
  skeleton with $i,k$ nonadjacent and $S$ is any set $d$-separating $i$ and
  $k$, then $i\to j\leftarrow k$ if and only if $j\notin S$. Consequently,
  under the global Markov property and faithfulness, an algorithm that
  removes the edge $i-j$ as soon as some conditioning set renders $i$ and $j$
  independent, searching sets of increasing size among current neighbors as
  the PC algorithm does, recovers the skeleton and the unshielded colliders,
  and hence the Markov equivalence class of item 15; Meek's rules then orient
  every edge common to the class. With Gaussian data and tests of vanishing
  partial correlation, the sample version is consistent for the class.

* **26. Identifiability of restricted structural equation models.** Suppose
  $X_j=\sum_{k\in\mathrm{pa}(j)}\beta_{jk}X_k+N_j$ along a directed acyclic
  graph $G$, with jointly independent noises and $\beta_{jk}\ne0$ for every
  edge. If the noises are non-Gaussian with strictly positive densities
  (the linear non-Gaussian acyclic model), or if they are Gaussian with a
  common variance, then $G$ is identifiable from the joint distribution.
  The same holds for $X_j=f_j(X_{\mathrm{pa}(j)})+N_j$ with Gaussian noises and
  three times differentiable functions $f_j$ that are nonlinear in each
  argument. By contrast, linear Gaussian models with unrestricted variances
  identify only the Markov equivalence class. The non-Gaussian case rests on
  the Darmois–Skitovič theorem.

## Reference guide

### Correspondence with the section

Rosenbaum carries randomization inference and sensitivity analysis. Pearl
carries directed interventions, the do-calculus, structural counterfactuals,
and probabilities of causation. Imbens and Rubin, and Ding, carry potential
outcomes, completely randomized, stratified, and paired experiments,
regression adjustment, and instrumental variables; Ding also carries the
E-value and the mediation formula. Hernán and Robins carry the $g$-formula,
marginal structural models, and time-varying treatments. Peters, Janzing,
and Schölkopf carry the graphical and structural-equation account,
including the identifiability of restricted structural equation models.
Spirtes, Glymour, and Scheines carry conditional-independence search. The efficiency theory used by the doubly
robust estimator is in Section 104.

### Source comparisons and local copies

For the expansion, Ding's Section 18.2 was read for sharp worst-case
bounds and Section 20.2.2, Theorem 20.2, for identification at a regression
discontinuity. Item 14 records the elementary two-period identification
identity under an explicit parallel-trends assumption. The variance in
item 11 is obtained from the efficient influence function by conditioning
on $X$. Items 4 and 11 use the sample-splitting conditions in SYNOPSIS104,
item 28, when fitted nuisances are evaluated on the observations.

The path-blocking definition and the covariate-kernel $g$-formula have
been written explicitly: an active path can contain noncolliders outside
the conditioning set, and treatment fixing in a longitudinal intervention
changes which covariate transition laws are integrated. A sharp-null
randomization test is SYNOPSIS106, item 15; its exactness does not extend
automatically to the weaker hypothesis of zero average treatment effect.

Item 1 is Ding's Theorem 4.1, including the divisor $n-1$ in $S^2$ and the
identity $\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)=S^2(\tau)/n$.
Item 8 is Pearl's Theorem 3.4.1. Item 4 records the product condition
$o_P(n^{-1/2})$ under which the estimated influence function is efficient.
Item 10 is the paired sensitivity model: the worst-case assignment
probability within a pair is $\Gamma/(1+\Gamma)$.

For the third expansion the following passages were read. Ding: Section
5.3 (stratified experiments, including the comparison (5.4) with complete
randomization) for item 16; Section 7.3 and Theorem 7.1 for item 17;
Section 6.2.2 and Proposition 6.2 for item 18, where the asymptotic
comparisons are Lin's (2013) results and the negative results Freedman's
(2008) as reported by Ding; Section 13.1, Theorem 13.1, for item 19;
Sections 23.4–23.6 and Theorem 23.1 for item 20; Theorem 17.1, Lemma 17.1,
and Definition 17.1 for item 21; Definition 27.1, Assumptions 27.2–27.5,
Theorem 27.1, and Example 27.4 for item 22; Problems 29.6–29.8, Theorems
29.6–29.8, for item 24. Pearl: Definitions 7.1.1–7.1.5 for structural
causal models, and Definitions 9.2.1–9.2.3, 9.2.9, 9.2.13 with Theorems
9.2.10, 9.2.11, 9.2.14, and 9.2.15 for item 23. Hernán and Robins,
Sections 12.3–12.4 and 21.2, for stabilized weights and marginal
structural models. Peters, Janzing, and Schölkopf: Lemma 7.8 and Section
7.2.1 for item 25, and Proposition 7.5 and Theorems 7.6–7.7 for item 26;
the consistency of the Gaussian PC algorithm is the result of Kalisch and
Bühlmann (2007) cited there. Matching estimators and their bias
(Abadie and Imbens) were not added: Ding's Chapter 15 gives the
bias-corrected estimator but not the rate theory, and the original papers
are not local.

Spirtes, Glymour, and Scheines, *Causation, Prediction, and Search*, and
van der Laan and Rose, *Targeted Learning*, are not in the local reference
directory. The local Rosenbaum file is the 2025 introduction; the 2002
monograph *Observational Studies* is not that file. Tsiatis,
*Semiparametric Theory and Missing Data*, is absent, as already recorded
for Section 104.

Local texts directly consulted or identified for this selection:

- [Ding, *A First Course in Causal Inference*](../lean-CKMA/References/Ding2024FirstCourseCausalInference-ChapmanHallCRC.TextsStatSci.pdf).
  Theorem 4.1 and the passages listed above were read.
- [Pearl, *Causality*](../lean-CKMA/References/Pearl2009CausalityModelsReasoningInference2ndEd-Cambridge.pdf).
  Theorem 3.4.1 and the Chapter 7 and 9 passages listed above were read.
- [Imbens and Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*](../lean-CKMA/References/ImbensRubin2015CausalInferenceStatisticsSocialBiomedicalSciencesIntroduction-Cambridge.pdf).
- [Hernán and Robins, *Causal Inference: What If*](../lean-CKMA/References/HernánRobins2020CausalInferenceWhatIf-ChapmanHallCRC.pdf).
- [Peters, Janzing, and Schölkopf, *Elements of Causal Inference*](../lean-CKMA/References/PetersJanzingSchölkopf2017ElementsCausalInferenceFoundationsLearningAlgorithms-MITPressAdaptiveCompMl.pdf).
- [Rosenbaum, *An Introduction to the Theory of Observational Studies*](../lean-CKMA/References/Rosenbaum2025IntroductionTheoryObservationalStudies-Springer.STS.pdf).
