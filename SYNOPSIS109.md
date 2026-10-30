# Synopsis: Causal inference

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-109).

This synopsis follows Section 109. The objects are potential outcomes and
interventions on directed graphical models. Missingness at random, the
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

## Reference guide

### Correspondence with the section

Rosenbaum carries randomization inference and sensitivity analysis. Pearl
carries directed interventions and the do-calculus. Imbens and Rubin, and
Ding, carry potential outcomes, completely randomized experiments, and
instrumental variables. Hernán and Robins carry the $g$-formula and
time-varying treatments. Peters, Janzing, and Schölkopf carry the graphical
and structural-equation account. Spirtes, Glymour, and Scheines carry
conditional-independence search. The efficiency theory used by the doubly
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

Spirtes, Glymour, and Scheines, *Causation, Prediction, and Search*, and
van der Laan and Rose, *Targeted Learning*, are not in the local reference
directory. The local Rosenbaum file is the 2025 introduction; the 2002
monograph *Observational Studies* is not that file. Tsiatis,
*Semiparametric Theory and Missing Data*, is absent, as already recorded
for Section 104.

Local texts directly consulted or identified for this selection:

- [Ding, *A First Course in Causal Inference*](../lean-CKMA/References/Ding2024FirstCourseCausalInference-ChapmanHallCRC.TextsStatSci.pdf).
  Theorem 4.1 was read.
- [Pearl, *Causality*](../lean-CKMA/References/Pearl2009CausalityModelsReasoningInference2ndEd-Cambridge.pdf).
  Theorem 3.4.1 was read.
- [Imbens and Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*](../lean-CKMA/References/ImbensRubin2015CausalInferenceStatisticsSocialBiomedicalSciencesIntroduction-Cambridge.pdf).
- [Hernán and Robins, *Causal Inference: What If*](../lean-CKMA/References/HernánRobins2020CausalInferenceWhatIf-ChapmanHallCRC.pdf).
- [Peters, Janzing, and Schölkopf, *Elements of Causal Inference*](../lean-CKMA/References/PetersJanzingSchölkopf2017ElementsCausalInferenceFoundationsLearningAlgorithms-MITPressAdaptiveCompMl.pdf).
- [Rosenbaum, *An Introduction to the Theory of Observational Studies*](../lean-CKMA/References/Rosenbaum2025IntroductionTheoryObservationalStudies-Springer.STS.pdf).
