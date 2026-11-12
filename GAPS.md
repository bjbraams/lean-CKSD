# Principal gaps in the core knowledge of statistics and data science

This file belongs to the project *Core Knowledge of Statistics and Data
Science*, which describes the statistics and data science expected of
graduate students and beginning researchers and compares it with the results
proved in the Lean libraries Mathlib, TauCeti, and Statlib. It follows the gap
inventory of the sibling analysis project,
[CKMA GAPS.md](../lean-CKMA/GAPS.md). The [bibliography](CKSD-bib.md) divides
the subject into Sections 101–109. For Sections 101–108, `SYNOPSISddd.md`
describes the mathematical content in numbered entries
([synopsis index](SYNOPSIS.md)), and `STRUCTUREddd.md` records how far
Mathlib, TauCeti, and Statlib cover those entries, with declarations, source locations
and hypotheses ([coverage index](STRUCTURE.md)). Section-by-section
summaries for each library are in [MathlibCoverage.md](MathlibCoverage.md),
[TauCetiCoverage.md](TauCetiCoverage.md), and
[StatlibCoverage.md](StatlibCoverage.md).

This catalogue selects **296 principal theorem statements and theorem
families** from the 537 synopsis entries for which Lean code would be a
genuine addition to the combined Mathlib, TauCeti, and Statlib core. The emphasis is
on the central theorems of each section, the results that organize its
theory, and the results that many others depend on. The catalogue does not
attempt to list every omitted lemma or every result in the reference books.

The comparison uses Mathlib at `6135ffb78e8bcd3fcc8ec02f3f82ea0b0737358b`
(5 November 2026), TauCeti at `afa08a3ed16fb167e35de371afb1eb03fbc5913a`
(6 November 2026), and Statlib at `eeaac0283690efaa60c31115400cf561836baeb9`
(5 November 2026), and rests on the coverage inventories, which were checked
by source inspection on 6 November 2026. Only completed proofs count as
library results; admissions, acquisition targets and roadmap text do not.
Library results are described here in words; the STRUCTURE files give the
declaration names and full hypotheses.

Statements are selected principally for requiring substantial mathematical
work beyond the combined libraries. A missing named declaration, a routine
specialization, finite algebraic bookkeeping, or repackaging in a new
definition does not by itself qualify. Some central theorems that none of
the libraries states are nevertheless selected although they follow from existing
results by a comparatively short argument; their assessments sketch that
argument, and [GAPS_EASY.md](GAPS_EASY.md) outlines it with the library
results used. Entries partly covered in the sense of [STRUCTURE.md](STRUCTURE.md)
are selected when the missing part is substantial, and their assessments say
what is present.

Numbers retain the synopsis provenance: **102.13** means entry 13 of
`SYNOPSIS102.md`. They are deliberately nonconsecutive. Statements have
occasionally been combined with neighbouring hypotheses or reformulated to
stand alone, without dropping any hypothesis of the synopsis entry; secondary
conclusions are sometimes omitted. Where a synopsis places entries directly
under a lettered subdivision, before its first topic heading, this file uses
the subdivision title as the topic heading. Each section links to its
mathematical synopsis and coverage inventory; the synopsis also supplies the
reference-text guide. The **numbered assertions**, at the scope specified in
each assessment, are the selected gaps. Counts refer to selected statements
or families, not to independent theorems or percentages of a subject.

The coverage counts use CKSD's direct-declaration rule, which differs
from some CKMA classifications; see [Comparison with CKMA](STRUCTURE.md#comparison-with-ckma).
The size of GAPS_EASY.md measures selected statements or delimited parts
with short mathematical derivations, not statements already proved in a
library or estimates of Lean implementation effort.

## Where the largest gaps lie

Statistics in the formal sense is thinly represented in the three libraries.
Of the 537 synopsis entries, 5 are covered and 55 partly covered by the
libraries together; the remaining 477 are not covered. No library has a
dedicated API for sufficient statistics, Fisher information, tests with size
and power, confidence sets, estimator sequences, learning rules, or Markov
decision processes. Measurable families of laws and randomized estimators are
represented by Markov kernels in Mathlib, with risk integrals and definitions
of average, Bayes, and minimax risk, and Statlib builds its binary testing
theory on that framework. The foundation on which further definitions would
rest is substantial. Mathlib contributes:

* probability: kernels, disintegration and conditional distributions,
  conditional expectation with the law of total variance, the strong law,
  the central limit theorem for independent identically distributed real
  variables with Lévy's continuity theorem, Cramér–Wold and Slutsky,
  discrete-time martingales, the Kolmogorov extension theorem, the maximal
  ergodic inequality, multivariate Gaussian laws, and sub-Gaussian and
  Hoeffding bounds;
* decision theory: risk, Bayes risk and minimax risk of randomized rules,
  the posterior kernel and Bayes estimators as posterior minimizers, and
  the easy comparison of experiments under garbling;
* information and geometry: Kullback–Leibler divergence with chain rule and
  data processing, total variation, exponential tilting, differentiation
  under the integral sign, reproducing-kernel Hilbert spaces, the VC
  dimension with the Sauer–Shelah bound, orthogonal projection, and
  Hausdorff and Gromov–Hausdorff distances.

TauCeti adds:

* exact distribution theory: quantiles and the probability integral
  transform, order statistics with their joint law, the chi-squared,
  Student, Fisher, Beta, Gamma and Dirichlet laws and their noncentral
  forms, the laws of projections of Gaussian vectors and their
  independence, Gaussian conditioning and quadratic forms, one-dimensional
  Gaussian integration by parts, a developed Wishart theory with the
  Bartlett decomposition and the determinant law, the von Mises–Fisher law,
  and the generalized extreme-value and generalized Pareto families;
* inequalities and spectra: Pinsker's, McDiarmid's, Bernstein's and Azuma's
  inequalities, sub-Gaussian matrix norm bounds, covering numbers, the Ky
  Fan, Courant–Fischer, Davis–Kahan, Yu–Wang–Samworth and Procrustes
  principles;
* processes, harmonic analysis and exchangeability: Markov-chain recurrence,
  period and coupling, renewal theory, Herglotz's and Bochner's theorems,
  Fourier inversion for measures, de Finetti's theorem, and the graphon form
  of the Aldous–Hoover theorem;
* transport and entropy: Fréchet and Wasserstein barycenters with
  consistency of empirical barycenters, the Gaussian Bures formula and
  fixed-point barycenters, the one-dimensional quantile isometry, entropic
  duality and the Sinkhorn divergence, the static and dynamic Schrödinger
  problems, the Benamou–Brenier formula, McCann's displacement convexity,
  iterative proportional fitting, JKO steps, Gromov–Wasserstein distances,
  and kernel mean embeddings with universal kernels characteristic.

Statlib adds:

* divergences: f-divergences, Hellinger, Rényi, Chernoff and Jensen–Shannon
  divergences, tensorization of the Kullback–Leibler divergence over finite
  products, conditional divergence, mutual information, statistical
  information, and integral and data-processing forms of total variation;
* testing and decision: the Bayes risk of binary tests with the
  total-variation testing identity, Bretagnolle–Huber, binary Fano and a
  Fano-type bound through mutual information, sample complexity of binary
  testing, and measurable Bayes rules under 0–1 loss;
* asymptotics and sequential analysis: definitions of contiguity and of
  differentiability in quadratic mean with the mean-zero score, likelihood
  ratios and divergences at stopping times, Wald's identity, e-variables
  and numeraires, and notation for potential responses.

The remaining gaps should be assessed relative to that combined foundation.
They are distributed by section as follows:

* [101. Statistical inference: foundations, decision theory, estimation, and testing](#101-statistical-inference-foundations-decision-theory-estimation-and-testing): 36 statements.
* [102. Asymptotic, semiparametric, and robust statistics](#102-asymptotic-semiparametric-and-robust-statistics): 35 statements.
* [103. Nonparametric and high-dimensional inference](#103-nonparametric-and-high-dimensional-inference): 30 statements.
* [104. Bayesian inference and stochastic computation](#104-bayesian-inference-and-stochastic-computation): 39 statements.
* [105. Linear models, multivariate analysis, experimental design, and causal inference](#105-linear-models-multivariate-analysis-experimental-design-and-causal-inference): 40 statements.
* [106. Dependent data and stochastic models](#106-dependent-data-and-stochastic-models): 28 statements.
* [107. Statistical learning and machine learning](#107-statistical-learning-and-machine-learning): 46 statements.
* [108. Geometry of data: manifolds, topology, optimal transport, and kernels](#108-geometry-of-data-manifolds-topology-optimal-transport-and-kernels): 42 statements.

The largest single gaps are the finite-sample theory of sufficiency,
information and optimal tests (101); the whole of statistical asymptotics,
from the delta method and maximum-likelihood theory through local asymptotic
normality and the rest of Le Cam's theory, the multivariate central limit
theorem, semiparametric efficiency and the bootstrap (102); empirical
processes, smoothing, the minimax rate theorems built on the two-point, Fano
and Assouad reductions, and sparse estimation (103); posterior asymptotics
and the convergence theory of Markov chain Monte Carlo and Langevin sampling
(104); the laws of general quadratic forms, the multivariate sampling theory
beyond the Wishart law, design optimality and the identification theory of
causal inference (105); limit theory for dependent data, counting processes
and extreme-value limit theory (106); generalization theory, approximation
by neural networks, bandits and reinforcement learning, and differential
privacy (107); and persistent homology together with the statistical rates
of optimal transport and kernel discrepancies (108).

## 101. Statistical inference: foundations, decision theory, estimation, and testing

None of the three libraries defines sufficiency, ancillarity, completeness,
Fisher information, tests with size and power, $p$-values, or confidence
sets. Mathlib already represents measurable parametrized models and
randomized estimators by Markov kernels. It supplies
the surrounding probability and a decision-theoretic vocabulary: risk, Bayes
risk and minimax risk for randomized rules given as Markov kernels, the
inequality between the maximal Bayes risk and the minimax risk, the posterior
kernel and Bayes estimators as posterior argmins, the easy direction of
Blackwell's comparison in integrated form, conditional Jensen,
differentiation under the integral sign, Sion's minimax theorem,
Kullback–Leibler divergence with its chain rule and data processing, and,
in one dimension, exponential tilting with the analyticity of the cumulant
function and its first two derivatives. TauCeti adds the chi-squared,
Student $t$ and Fisher $F$ laws and their noncentral versions with their
ratio representations, the chi-squared laws and independence of orthogonal
projections of a standard Gaussian vector, the joint law of the order
statistics of an atomless sample and the laws of single order statistics,
the probability integral transform, binomial-tail and beta-quantile
identities, tensorization of relative entropy, Pinsker's inequality, Stein's
identity in dimension one, and the determination of a law on the line by
its moment generating function near zero. Statlib assesses simple binary
tests by their Bayes risk under the $0$–$1$ loss, with the likelihood-ratio
test as a Bayes test and the testing identity for total variation, and adds
measurable Bayes rules for the $0$–$1$ loss, concavity of the Bayes risk,
the $n$-fold tensorization of relative entropy, and refinements of the easy
half of Blackwell's comparison. The divergence identities of 101.44 and the
testing bound of 101.66 are covered. Missing is the whole finite-sample
theory proper: sufficiency and completeness, the information inequality, the
Neyman–Pearson theory with its unbiased and invariant refinements, the
multiparameter geometry of exponential families, admissibility and complete
classes, equivariance, shrinkage, and the converse half of Blackwell's
theorem. The joint law of the normal sample mean and variance, and
Scheffé's simultaneous intervals, are short arguments from TauCeti's
projection theorems but are not stated.

Sources: [mathematical synopsis](SYNOPSIS101.md); [combined coverage inventory](STRUCTURE101.md).

Throughout, a statistical model is a family $\{P_\theta:\theta\in\Theta\}$
of probability measures on a measurable space $(\mathcal X,\mathcal A)$. It
is **dominated** by a $\sigma$-finite measure $\mu$ when each $P_\theta$ has
a density $f(\cdot\mid\theta)$ with respect to $\mu$; the **likelihood** of
$x$ is $\theta\mapsto f(x\mid\theta)$. A **statistic** is a measurable map
on $\mathcal X$; an estimator of $g(\theta)$ is **unbiased** when it is
integrable with expectation $g(\theta)$ for every $\theta$. Samples are
independent and identically distributed of size $n$ unless stated
otherwise.

For a dominated model on a standard Borel space, a statistic $T$ is
**sufficient** when the regular conditional distribution of the observation
given $T$ can be chosen independent of $\theta$, and
**ancillary** when its law does not depend on $\theta$. A family of laws is
**complete** for $T$ when $\mathbb E_\theta g(T)=0$ for every $\theta$
forces $g(T)=0$ almost surely under every $\theta$, the expectations being
assumed to exist; **boundedly complete** when this is required only for
bounded $g$. A **test** is a measurable
function $\varphi$ with values in $[0,1]$; its expectation is the **size**
at a null point and the **power** at an alternative. A test is **uniformly
most powerful** (UMP) of level $\alpha$ when, among tests of size at most
$\alpha$ on the null set, it maximizes the power at every alternative. A
family has **monotone likelihood ratio** in a real statistic $T$ when
$f(\cdot\mid\theta_2)/f(\cdot\mid\theta_1)$ is a nondecreasing function of
$T$ for $\theta_2>\theta_1$.

### Sufficiency, likelihood, and minimal reduction

* **101.1. Factorization theorem.** Let the model be dominated by a
  $\sigma$-finite measure $\mu$. A statistic $T$ is sufficient if and only
  if there exist nonnegative measurable functions $g_\theta$ and $h$ with
  $f(x\mid\theta)=g_\theta(T(x))\,h(x)$ for $\mu$-almost every $x$ and
  every $\theta$. No library defines sufficiency; Mathlib supplies
  Radon–Nikodým derivatives, regular conditional distributions and
  disintegration on standard Borel spaces. Missing are the definition and
  the theorem, including the Halmos–Savage reduction of a dominated family
  to a countable equivalent subfamily.

* **101.2. Minimal sufficiency.** Let the model be
  dominated by $\mu$ with a common support $\mathcal X_0$ for all
  $\theta$, fix $\theta_0$, and put
  $\lambda_\theta=f(\cdot\mid\theta)/f(\cdot\mid\theta_0)$ on
  $\mathcal X_0$. The map $x\mapsto(\lambda_\theta(x))_{\theta\in\Theta}$,
  with the product $\sigma$-algebra on $\mathbb R^\Theta$, is sufficient,
  and for every sufficient $S$ and every $\theta$ there is a measurable
  $\varphi_\theta$ with $\lambda_\theta=\varphi_\theta\circ S$ almost
  everywhere on $\mathcal X_0$. When $\Theta$ is countable, or the sample
  space is countable with counting measure, a statistic $T$ with values in
  a standard Borel space such that, for all $x,y\in\mathcal X_0$,
  $T(x)=T(y)$ exactly when $\theta\mapsto f(x\mid\theta)$ and
  $\theta\mapsto f(y\mid\theta)$ are positive scalar multiples of one
  another is minimal sufficient: $T$ is sufficient and, for every
  sufficient $S$, there is a set $N$ with $P_\theta(N)=0$ for every
  $\theta$ such that $T(x)=T(y)$ whenever $x,y\notin N$ and $S(x)=S(y)$.
  The libraries have only the log-likelihood ratio of two measures
  (Mathlib) and, in Statlib, the statement that restricting two finite
  measures $\mu,\nu$ to the $\sigma$-algebra generated by
  $d\mu/d(\mu+\nu)$ leaves every $f$-divergence unchanged, the divergence
  form of the sufficiency of the likelihood ratio for a pair of laws.

### Exponential families

A dominated family is a **natural exponential family** of order $k$ when
$f(x\mid\eta)=h(x)\exp(\eta\cdot T(x)-A(\eta))$; the **natural parameter
space** $\mathcal N$ is the set where $\exp A(\eta)$ is finite. The
representation is **minimal** when neither the law of $T$ nor $\mathcal N$
lies in a proper affine subspace, and **full rank** when the parameter set
has nonempty interior in $\mathcal N$.

* **101.4. Structure of a full-rank exponential family.** The natural
  parameter space is convex. On its interior $A$ is real analytic,
  $\nabla A(\eta)=\mathbb E_\eta T$ and
  $\mathop{\mathrm{Hess}}A(\eta)=\mathop{\mathrm{Cov}}_\eta(T)$. In a
  minimal representation the Hessian is positive definite on the interior,
  so the family is identifiable in the mean parameter. For an independent
  sample, the sum of the copies of $T$ is a natural sufficient statistic
  whose law is the exponential family with the same natural parameter and
  cumulant function $nA$. Mathlib proves the one-parameter case of the
  first three claims for the tilted measure: the exponential-integrability
  set is an interval, the cumulant generating function is analytic on its
  interior, and its first two derivatives are the tilted mean and variance.
  TauCeti computes the generating functions of a tilted law and proves the
  Gaussian, gamma, Poisson and binomial families closed under tilting, with
  explicit parameter maps, without a general definition of an exponential
  family. Missing are the multiparameter form, positive definiteness,
  identifiability, and the sample-sum statement.

* **101.5. Completeness in a full-rank exponential family.** In a minimal
  full-rank exponential family the natural statistic $T$ is complete: if
  $\mathbb E_\eta g(T)=0$ for every $\eta$ in a nonempty open set, then
  $g(T)=0$ almost surely under every such $\eta$. TauCeti proves that a
  finite measure on the line with finite exponential moments near zero is
  determined by its moment generating function there, which after a tilt
  to the centre of the open set and a split of $g$ into positive and
  negative parts gives the one-parameter case by a short argument.
  Completeness itself is not formulated, and the case $k>1$ needs the
  multivariate uniqueness theorem for Laplace transforms.

* **101.6. Pitman–Koopman–Darmois theorem, monotone form.** Let
  $\mathcal P$ be a family of mutually absolutely continuous laws on
  $(\mathcal X,\mathcal A)$, each equivalent to a law $P_0$. Suppose that
  for every $n$ in an infinite set $\mathbb N_0\subset\mathbb N$ containing
  $1$ there are a measurable $T_n:\mathcal X^n\to\mathbb R$ and
  nondecreasing functions $H_{P,n}$ such that $H_{P,n}\circ T_n$ is a
  $P_0^n$-density of $P^n$ for every $P\in\mathcal P$. Then there are a
  measurable $S:\mathcal X\to\mathbb R$ and functions
  $C:\mathcal P\to(0,\infty)$ and $a:\mathcal P\to\mathbb R$ such that
  $C(P)\exp(a(P)S)$ is a $P_0$-density of $P$ for every $P$: the family is
  a one-parameter exponential family. None of the three libraries has any
  part of this statement.

### Unbiased estimation and information

The **Fisher information** of a real parameter, when the support does not
depend on $\theta$ and the score $\partial_\theta\log f(X\mid\theta)$ is
square-integrable, is
$I(\theta)=\mathbb E_\theta(\partial_\theta\log f(X\mid\theta))^2$; for a
parameter in an open subset of $\mathbb R^k$ the information matrix is the
covariance of the score vector.

* **101.7. Rao–Blackwell theorem.** Let $T$ be sufficient and let $\delta$
  be an estimator with $\mathbb E_\theta|\delta|<\infty$. Then
  $\delta^\star(T)=\mathbb E_\theta[\delta\mid T]$ does not depend on
  $\theta$, has the same expectation as $\delta$, and, for a loss
  $L(\theta,a)$ convex in $a$, satisfies
  $\mathbb E_\theta L(\theta,\delta^\star(T))\le
  \mathbb E_\theta L(\theta,\delta(X))$. Mathlib's conditional Jensen
  inequality gives the risk reduction for a single law after taking
  expectations; the theorem follows by that short argument once sufficiency
  is defined, which supplies the independence of $\theta$.

* **101.8. Lehmann–Scheffé theorem.** Let $T$ be a complete sufficient
  statistic and let $g(\theta)$ admit an unbiased estimator of finite
  expectation. Then there is an unbiased estimator $\varphi(T)$; any two
  unbiased functions of $T$ agree almost surely under every $P_\theta$; and
  for every loss convex in the action, $\varphi(T)$ minimizes the risk
  among all unbiased estimators of finite risk. It follows from 101.7 and
  completeness by a short argument, but none of the notions involved is
  defined.

* **101.9. Basu's theorem.** If $T$ is a boundedly complete sufficient
  statistic and $V$ is ancillary, then $T$ and $V$ are independent under
  every $P_\theta$. Not present in any of the three libraries.

* **101.10. Information inequality.** Let $\theta$ range over an open
  subset of $\mathbb R^k$, let the support be free of $\theta$, the density
  differentiable in $\theta$, and the information matrix $I(\theta)$
  nonsingular. Let $W$ be an unbiased estimator of a differentiable
  $g:\Theta\to\mathbb R^m$ with $\mathbb E_\theta\|W\|^2<\infty$, and
  assume that differentiation in each $\theta_j$ may be passed under the
  integrals $\int Wf(\cdot\mid\theta)\,d\mu$ and
  $\int f(\cdot\mid\theta)\,d\mu$. Then
  $$\mathop{\mathrm{Cov}}_\theta(W)
  \ge Dg(\theta)\,I(\theta)^{-1}\,Dg(\theta)^\top$$
  in the Loewner order; for a real parameter,
  $\mathop{\mathrm{Var}}_\theta W\ge g'(\theta)^2/I(\theta)$, and for an
  independent sample $I(\theta)$ is replaced by $nI_1(\theta)$. Fisher
  information and the score are not defined. The ingredients are available
  in general form: Mathlib's differentiation under the integral sign with a
  dominated derivative, covariance bilinearity and Cauchy–Schwarz, and the
  Loewner order. Statlib's quadratic-mean differentiability, with a score
  of mean zero, is a starting point for the score under weaker regularity.

### Minimum-variance unbiased estimators beyond the information bound

* **101.12. Characterization of UMVU estimators.** Let $W$ be an unbiased
  estimator of $g(\theta)$ with $\mathbb E_\theta W^2<\infty$ for every
  $\theta$. Then $W$ has minimal variance at every $\theta$ among unbiased
  estimators $W'$ of $g(\theta)$ with $\mathbb E_\theta W'^2<\infty$ for every
  $\theta$ if and only if
  $\mathop{\mathrm{Cov}}_\theta(W,U)=0$ for every $\theta$ and every
  statistic $U$ with $\mathbb E_\theta U=0$ and
  $\mathbb E_\theta U^2<\infty$ for every $\theta$. If $T$ is sufficient
  and $W=h(T)$, it suffices to test functions $U$ of $T$. Such an estimator
  is unique almost surely under every $P_\theta$. Mathlib's $L^2$
  projection property of conditional expectation is the underlying
  Hilbert-space fact; the statement is absent.

* **101.13. Completeness of the order statistic.** Let $\mathcal P$ be a
  complete family of laws on $(\mathcal X,\mathcal A)$ that is closed under
  finite convex combinations. Then for every $n$ the $\sigma$-algebra of
  permutation-invariant events in $\mathcal X^n$ is complete for
  $\{P^n:P\in\mathcal P\}$ (and it is always sufficient). This applies to
  all laws on $\mathbb R^d$ with a Lebesgue density, to all laws on
  $\mathbb R$ with continuous distribution function, and to the laws with
  a Lebesgue density and prescribed finite absolute moments. Consequently,
  for a symmetric kernel $h$ integrable under every $P^m$ and $n\ge m$, the
  $U$-statistic
  $$U_n=\binom nm^{-1}\sum_{i_1<\cdots<i_m}h(X_{i_1},\ldots,X_{i_m})$$
  is the unique symmetric unbiased estimator of
  $\mathbb E_Ph(X_1,\ldots,X_m)$ and minimizes the risk among unbiased
  estimators for every loss convex in the action. TauCeti computes the
  mean-square error of a sample mean but states no optimality; the theorem
  is absent.

### Tests and confidence sets

* **101.14. Neyman–Pearson lemma.** Let $P_0,P_1$ have densities
  $f_0,f_1$ with respect to $\mu$ and let $0<\alpha<1$. There are $k\ge0$
  and a test $\varphi$ with $\mathbb E_{P_0}\varphi=\alpha$, $\varphi=1$
  where $f_1>kf_0$ and $\varphi=0$ where $f_1<kf_0$. Any such test is most
  powerful of level $\alpha$, and every most powerful level-$\alpha$ test
  agrees with it $(P_0+P_1)$-almost everywhere off $\{f_1=kf_0\}$. Statlib
  treats a simple binary test as a Markov kernel into $\{0,1\}$ assessed by
  its Bayes risk under the $0$–$1$ loss: for prior weights $\pi_0,\pi_1$ the
  Bayes risk is the infimum over measurable regions $E$ of
  $\pi_0P_0(E)+\pi_1P_1(E^c)$, and the likelihood-ratio test that decides
  for $P_1$ where $\pi_0\,dP_0\le\pi_1\,dP_1$ is a Bayes test. This is the
  Lagrangian form of the construction; tests of prescribed size, the
  existence of $k$ and of the randomization, and uniqueness are not stated
  in any library. Optimality follows from the pointwise inequality
  $(\varphi-\varphi')(f_1-kf_0)\ge0$ by integration; existence of $k$ and
  the randomization constant uses the distribution function of $f_1/f_0$
  under $P_0$.

* **101.15. Karlin–Rubin theorem.** Let the family, with
  $\Theta\subset\mathbb R$, have monotone likelihood ratio in $T$. For
  $\theta_0\in\Theta$ and $0<\alpha<1$, every test with $\varphi=1$ for
  $T>c$, $\varphi=\gamma$ for $T=c$, $\varphi=0$ for $T<c$, and size
  $\alpha$ at $\theta_0$, is UMP of level $\alpha$ for $\theta\le\theta_0$
  against $\theta>\theta_0$, and its power function is nondecreasing. In
  particular the one-sided test on the natural statistic of a
  one-parameter exponential family is UMP. Absent; it follows from 101.14
  applied pointwise in the alternative.

* **101.17. Gaussian sampling distributions.** For independent
  $X_1,\ldots,X_n\sim N(\mu,\sigma^2)$, $\sigma>0$, $n\ge2$, with
  $\bar X=n^{-1}\sum_iX_i$ and $S^2=(n-1)^{-1}\sum_i(X_i-\bar X)^2$:
  $\bar X\sim N(\mu,\sigma^2/n)$, $(n-1)S^2/\sigma^2\sim\chi^2_{n-1}$, and
  $\bar X$ and $S^2$ are independent. Hence $\sqrt n(\bar X-\mu)/S$ has the
  Student $t_{n-1}$ law and
  $\bar X\pm t_{n-1,1-\alpha/2}S/\sqrt n$ has exact coverage $1-\alpha$;
  for two independent normal samples, each of size at least two,
  $(S_1^2/\sigma_1^2)/(S_2^2/\sigma_2^2)$ has the $F$ law with the sample
  sizes minus one as degrees of freedom. Mathlib gives the law of
  $\bar X$. TauCeti gives the known-mean chi-squared law, the
  representations of $t$ and $F$ as ratios of independent Gaussian and
  chi-squared variables, and, for the standard Gaussian on a Euclidean
  space, the independence of its orthogonal projections onto mutually
  orthogonal subspaces and the $\chi^2_{\dim K}$ law of the squared length
  of its projection onto a subspace $K$. Missing is the identification of
  $(n-1)S^2/\sigma^2$ with the squared projection of the standardized
  sample onto the orthogonal complement of the constant vectors, and of
  $\bar X$ with a function of the projection onto the constants. The chi-squared
  law of $S^2$ and its independence from $\bar X$ then follow from the
  projection theorems by a short argument, and the rest from the ratio
  theorems.

### Order statistics and exact confidence procedures

* **101.21. Distribution of order statistics.** For independent
  observations with continuous distribution function $F$ and density $f$,
  the order statistics have joint density $n!\prod_if(x_i)$ on
  $x_1<\cdots<x_n$, and $X_{(j)}$ has density
  $$\frac{n!}{(j-1)!(n-j)!}F(x)^{j-1}(1-F(x))^{n-j}f(x).$$
  In particular $F(X_{(j)})\sim\mathop{\mathrm{Beta}}(j,n+1-j)$, and the
  ranks are uniform on the $n!$ permutations and independent of the
  ordered sample. TauCeti proves that the law of the sorted sample of an
  atomless independent identically distributed sample is $n!$ times the
  product law restricted to the strictly increasing chamber, and, for
  every law, atoms included, the distribution function of a single order
  statistic and its representation as the quantile image of a beta law.
  The joint density is one step from the chamber formula, and the beta law
  of $F(X_{(j)})$ two steps from the quantile representation and the
  probability integral transform. Missing are the explicit marginal
  density for general $F$, and the law of the ranks with its independence
  from the order statistic.

### Finite decision problems

A **randomized decision rule** is a Markov kernel from the sample space to
the action space $\mathcal A$; its **risk** is
$R(\theta,\delta)=\mathbb E_\theta L(\theta,\delta(X))$, its **Bayes risk**
under a prior $\pi$ is $\int R(\theta,\delta)\,\pi(d\theta)$, and it is
**minimax** when it minimizes $\sup_\theta R(\theta,\delta)$. A rule is
**admissible** when no other rule has risk at most its risk everywhere and
strictly smaller somewhere.

* **101.32. Value of a finite statistical game.** If $\Theta$ and
  $\mathcal A$ are finite, the minimax risk equals the supremum over priors
  of the minimal Bayes risk, a minimax rule exists, and a least favorable
  prior exists. Mathlib proves that the maximal Bayes risk is at most the
  minimax risk and proves Sion's minimax theorem. The equality follows by
  identifying randomized rules on a finite action space, through their
  risk vectors, with a compact convex set on which the Bayes risk is
  bilinear, and applying Sion's theorem; this identification and the
  existence statements are missing.

* **101.37. Complete classes.** Let $\Theta$ be finite. Every admissible
  rule is Bayes for some prior. If the risk set
  $\{(R(\theta,\delta))_\theta\}\subset\mathbb R^\Theta$ of randomized
  rules is bounded from below and closed from below (it contains every
  point $x$ of its closure such that no other point $y$ of the closure has
  $y\le x$ coordinatewise), then the Bayes rules
  form a complete class and the admissible Bayes rules a minimal complete
  class. With the loss bounded below, both conditions hold when the action
  space is finite, or a closed bounded subset of Euclidean space with
  $a\mapsto L(\theta,a)$ continuous. Admissibility and complete classes are
  not defined; the separating-hyperplane argument is absent.

### Equivariance

A group $G$ acts measurably on the sample space, on $\Theta$ and on
$\mathcal A$; model and loss are **invariant** when $g$ pushes $P_\theta$ to
$P_{g\theta}$ and $L(g\theta,ga)=L(\theta,a)$, and a rule is
**equivariant** when it intertwines the actions on samples and on actions.

* **101.39. Hunt–Stein theorem, compact form.** Let the model and the loss
  be invariant, the loss bounded below, and $G$ a compact group with
  normalized Haar measure $\nu$ acting jointly measurably on samples,
  parameters and actions. For every randomized rule $\delta$, Haar
  averaging gives an equivariant randomized rule $\bar\delta$ with
  $R(\theta,\bar\delta)=\int_GR(g\theta,\delta)\,\nu(dg)$. Hence the maximum
  risk does not increase, the minimax value equals the infimum of the
  maximum risk over equivariant rules, and an equivariant minimax rule
  exists whenever a minimax rule exists. Mathlib's Haar measure is the
  starting point; group actions on models are not formulated.

* **101.40. Pitman estimator of location.** Let $X_1,\ldots,X_n$ be
  independent with density $f(x-\theta)$ on $\mathbb R$, with squared
  error loss, and suppose some location-equivariant estimator has finite
  risk. Then the minimum-risk equivariant estimator exists, is unique
  almost surely, and equals
  $$\delta(X)=\frac{\int u\prod_{i=1}^nf(X_i-u)\,du}
  {\int\prod_{i=1}^nf(X_i-u)\,du}.$$
  Its risk is finite and constant, and it is minimax among all estimators
  (Girshick–Savage). Not present in any of the three libraries.

### Exponential families and discrimination information

* **101.42. Mean parameterization.** Let the family be minimal with
  natural parameter space $\mathcal N$ of nonempty interior
  $\mathcal N^\circ$, and let $K^\circ$ be the interior of the convex hull
  of the support of the law of $T$. Then $\nabla A$ is a real-analytic
  diffeomorphism of $\mathcal N^\circ$ onto an open subset of $K^\circ$.
  If the family is **steep**, that is $\mathbb E_\eta\|T\|=\infty$ for
  every $\eta\in\mathcal N\setminus\mathcal N^\circ$ (in particular if
  $\mathcal N$ is open), the image is all of $K^\circ$. The covariance of
  $T$ under $P_\eta$ is $\nabla^2A(\eta)$. Only the one-dimensional
  covariance statement is in Mathlib, as the tilted variance; the
  diffeomorphism, steepness, and the identification of the mean domain are
  missing.

* **101.43. Conditional exponential families.** Let the natural statistic
  split as $(T,S)$ with natural parameter $(\eta,\zeta)$. There are
  measures $\nu_s$, free of $(\eta,\zeta)$, such that for almost every $s$
  the conditional law of $T$ given $S=s$ has density
  $t\mapsto\exp(\eta\cdot t-A_s(\eta))$ with respect to $\nu_s$, where
  $A_s(\eta)=\log\int e^{\eta\cdot t}\,\nu_s(dt)$; in particular it is free
  of $\zeta$. Mathlib's disintegration is available, but exponential
  families are not defined and the statement is absent.

### Unbiased tests in exponential families

A level-$\alpha$ test is **unbiased** when its power is at least $\alpha$
on the alternative, and **uniformly most powerful unbiased** (UMPU) when it
maximizes the power at every alternative among unbiased level-$\alpha$
tests.

* **101.45. Two-sided tests in a one-parameter exponential family.** In a
  minimal exponential family of order one with natural statistic $T$ and
  natural parameter in an open interval, a test of $\eta=\eta_0$ against
  $\eta\ne\eta_0$ that rejects for extreme values of $T$, randomizes only
  at the two critical points, and satisfies
  $\mathbb E_{\eta_0}\varphi(T)=\alpha$ and
  $\mathbb E_{\eta_0}[T\varphi(T)]=\alpha\,\mathbb E_{\eta_0}T$, is UMPU of
  level $\alpha$. Absent from all three libraries.

* **101.46. Conditional tests with a nuisance parameter.** In a minimal
  exponential family with natural statistic $(T,S)$, $T$ real, and natural
  parameter $(\eta,\zeta)$ in an open convex set meeting the hyperplane
  $\eta=\eta_0$, the two-sided test of 101.45 applied to the conditional
  law of $T$ given $S$, with conditional size $\alpha$, is UMPU of level
  $\alpha$ for $\eta=\eta_0$ against $\eta\ne\eta_0$; the conditional
  one-sided test is UMPU for a one-sided hypothesis on $\eta$. Absent; it
  combines 101.43, 101.45, 101.48 and 101.49.

### The generalized Neyman–Pearson lemma and similar tests

For hypotheses $\Theta_0,\Theta_1$ the boundary is
$\omega=\overline{\Theta_0}\cap\overline{\Theta_1}$. A test is
**$\alpha$-similar** on $\omega$ when its size is $\alpha$ at every point
of $\omega$, and has **Neyman structure** with respect to a statistic $T$
sufficient on $\omega$ when $\mathbb E_\theta[\varphi\mid T]=\alpha$ almost
surely for every $\theta\in\omega$.

* **101.47. Generalized Neyman–Pearson lemma.** Let
  $f_0,f_1,\ldots,f_m$ be $\mu$-integrable real functions,
  $k_1,\ldots,k_m$ real, and $\varphi_0$ a test equal to $1$ where
  $f_0>\sum_ik_if_i$ and to $0$ where $f_0<\sum_ik_if_i$. Then
  $\varphi_0$ maximizes $\int\varphi f_0\,d\mu$ among tests with
  $\int\varphi f_i\,d\mu\le\int\varphi_0f_i\,d\mu$ when $k_i>0$ and
  $\int\varphi f_i\,d\mu\ge\int\varphi_0f_i\,d\mu$ when $k_i<0$, in
  particular among tests with equality for every $i$. Absent; the proof is
  the pointwise argument of 101.14.

* **101.49. Neyman structure.** If $T$ is boundedly complete and
  sufficient for $\{P_\theta:\theta\in\omega\}$, then every
  $\alpha$-similar test on $\omega$ has Neyman structure with respect to
  $T$, so maximizing power among similar tests reduces to maximizing
  conditional power given $T=t$ subject to conditional size $\alpha$.
  Absent; it needs the notions of bounded completeness and sufficiency.

### Interval hypotheses in one-parameter exponential families

* **101.50. Uniformly most powerful tests of a two-sided hypothesis.** In
  a minimal exponential family of order one with natural statistic $T$ and
  natural parameter in an open interval containing $\eta_1<\eta_2$, and
  for $0<\alpha<1$, there is a test of $\eta\le\eta_1$ or $\eta\ge\eta_2$
  against $\eta_1<\eta<\eta_2$ with $\varphi=1$ for $c_1<T<c_2$,
  $\varphi=\gamma_i$ at $T=c_i$, $\varphi=0$ for $T<c_1$ or $T>c_2$,
  where $c_1\le c_2$, and
  $\mathbb E_{\eta_1}\varphi=\mathbb E_{\eta_2}\varphi=\alpha$. It is UMP
  of level $\alpha$, and among tests with the same power at $\eta_1$ and
  $\eta_2$ it minimizes the power at every $\eta<\eta_1$ and every
  $\eta>\eta_2$. Absent from all three libraries.

### Unbiased confidence sets and complete classes of tests

* **101.53. Karlin–Rubin complete class theorem.** Let a real-parameter
  family have monotone likelihood ratio in $T$, let the action space be
  $\{0,1\}$ (accept, reject), and let $L(\theta,1)-L(\theta,0)$ be
  positive for $\theta<\theta_0$ and negative for $\theta>\theta_0$. Then
  the one-sided tests ($\varphi=1$ for $T>c$, $\gamma$ at $T=c$, $0$ for
  $T<c$, with $c\in[-\infty,\infty]$, $\gamma\in[0,1]$) form an essentially
  complete class: every test has a one-sided test with risk no larger at
  every $\theta$. Absent from all three libraries.

### Least favorable distributions

For a measurably indexed null family $\{P_\vartheta:\vartheta\in\Theta_0\}$
and a probability $\Lambda$ on $\Theta_0$, write
$P_\Lambda=\int P_\vartheta\,\Lambda(d\vartheta)$.

* **101.54. Least favorable distributions.** Let $\varphi_0$ be most
  powerful of level $\alpha$ for $P_{\Lambda_0}$ against a simple
  alternative $Q$, and suppose $\mathbb E_\vartheta\varphi_0\le\alpha$ for
  every $\vartheta\in\Theta_0$. Then $\varphi_0$ is most powerful of level
  $\alpha$ for the composite null against $Q$, and $\Lambda_0$ is least
  favorable: no other mixture $P_\Lambda$ gives a smaller most powerful
  power against $Q$. If the power of $\varphi_0$ is below one, $\Lambda_0$
  is concentrated on $\{\vartheta:\mathbb E_\vartheta\varphi_0=\alpha\}$.
  Mathlib provides the mixtures as compositions of a measure with a
  kernel; the testing statement is absent.

### Invariant tests

A group acting on the sample space leaves a testing problem invariant when
it maps each $P_\theta$ to some $P_{\bar g\theta}$ with $\bar g$ preserving
$\Theta_0$ and $\Theta_1$. A statistic $M$ is a **maximal invariant** when
it is invariant and $M(x)=M(x')$ implies $x'=gx$ for some $g$.

* **101.55. Reduction by a maximal invariant.** A test is invariant if and
  only if it is a function of a maximal invariant $M$, and the law of an
  invariant statistic depends on $\theta$ only through a maximal invariant
  $v(\theta)$ of the induced group on $\Theta$. Hence the Neyman–Pearson
  lemma or the Karlin–Rubin theorem applied to the laws of $M$ yields a
  uniformly most powerful invariant test whenever these laws are simple
  against simple, or have monotone likelihood ratio in $v(\theta)$ for
  one-sided hypotheses. Absent from all three libraries; TauCeti defines
  the order statistic of a tuple but does not state its maximal
  invariance under permutations.

* **101.56. Normal tests as uniformly most powerful invariant tests.** For
  a sample from $N(\mu,\sigma^2)$, $\sigma>0$, $n\ge2$, work with the
  sufficient statistic $(\bar X,S^2)$. On this reduced sample space with
  $S>0$, an event of probability one, positive rescaling
  $(\bar x,s^2)\mapsto(c\bar x,c^2s^2)$, $c>0$, has maximal invariant
  $t=\sqrt n\bar X/S$. Its noncentral $t$ law on $n-1$ degrees of freedom,
  with noncentrality $\sqrt n\mu/\sigma$, has monotone likelihood ratio
  in $t$; the one-sided $t$ test is uniformly most powerful invariant for
  $\mu\le0$ against $\mu>0$. For $\mu=0$ against $\mu\ne0$, adjoining
  reflection gives the maximal invariant $|t|$ and the two-sided $t$ test.
  For two independent normal samples with a common unknown variance,
  reduce to their means and pooled variance $(\bar X,\bar Y,S_p^2)$.
  For sample sizes $m,n\ge1$ with $m+n\ge3$, common translations and
  positive rescalings give the pooled two-sample $t$ statistic as maximal
  invariant on $S_p>0$; adjoining reflection gives its absolute value.
  The corresponding one- and two-sided tests are uniformly most powerful
  invariant. For variance hypotheses with unknown mean, translations
  acting on $(\bar X,S^2)$ have maximal invariant $S^2$, giving the
  one-sided uniformly most powerful invariant chi-squared tests. TauCeti
  defines the noncentral $t$ law, with density and distribution function,
  and proves that it is the law of $(Z+\delta)/\sqrt{V/\nu}$ for
  independent $Z\sim N(0,1)$ and $V\sim\chi^2_\nu$. Its monotone likelihood
  ratio and the optimality statements are not stated, and the
  identification of the law of $t$ depends on 101.17; the statement also
  depends on 101.55.

### The normal mean and simultaneous coverage

* **101.57. Estimation of a normal mean.** Let $X\sim N_p(\theta,I_p)$
  with squared Euclidean loss. The estimator $X$ has risk $p$, which is
  the minimax risk; it is admissible for $p=1,2$ and inadmissible for
  $p\ge3$. The James–Stein estimator
  $(1-(p-2)/\|X\|^2)X$ has risk
  $p-(p-2)^2\mathbb E_\theta\|X\|^{-2}<p$ for every $\theta$, tending to
  $p$ as $\|\theta\|\to\infty$, and its positive-part version has risk no
  larger at every $\theta$. Admissibility is not defined, and Gaussian
  integration by parts (101.64) is proved only in dimension one, in
  TauCeti, for everywhere-differentiable functions.

### Admissibility by limits of Bayes rules

* **101.58. Blyth's method.** Let $\Theta$ be a convex subset of Euclidean
  space with nonempty interior, let the rules with continuous risk form a
  complete class, and let $\delta_0$ have continuous risk. Suppose there
  are finite, possibly unnormalized, priors $\pi_n$ with Bayes rules
  $\delta_n$ such that $r(\pi_n,\delta_0)$ and $r(\pi_n,\delta_n)$ are
  finite; for every convex $C\subset\Theta$ with nonempty interior there
  are $K>0$ and $N$ with $\pi_n(C)\ge K$ for $n\ge N$; and
  $r(\pi_n,\delta_0)-r(\pi_n,\delta_n)\to0$. Then $\delta_0$ is
  admissible. For $X\sim N(\theta,1)$ the priors
  $e^{-\theta^2/(2n)}\,d\theta$ prove admissibility of $X$. Mathlib's Bayes
  risk accepts unnormalized priors, but admissibility is not defined and
  the theorem is absent.

### Simultaneous coverage

* **101.60. Scheffé's method.** In the normal linear model
  $Y=X\beta+\varepsilon$, $\varepsilon\sim N_n(0,\sigma^2I_n)$, with $X$
  of rank $r<n$, let $\hat\beta$ be a least-squares estimator,
  $\hat\sigma^2=\|Y-X\hat\beta\|^2/(n-r)$, and $C$ the column space of
  $X^\top$. Then
  $$\sup_{c\in C\setminus\{0\}}
  \frac{(c\cdot(\hat\beta-\beta))^2}{\hat\sigma^2\,c^\top(X^\top X)^-c}
  =\frac{(\hat\beta-\beta)^\top X^\top X(\hat\beta-\beta)}{\hat\sigma^2},$$
  which has the law of $rF_{r,n-r}$, so the intervals
  $c\cdot\hat\beta\pm\hat\sigma\sqrt{rF_{r,n-r,1-\alpha}\,c^\top(X^\top X)^-c}$,
  $c\in C$, have exact simultaneous coverage $1-\alpha$. TauCeti has the
  $F$ law as a ratio of independent chi-squared laws, the moment
  generating function of Gaussian quadratic forms, and the chi-squared
  laws and independence of the projections of a standard Gaussian vector
  onto mutually orthogonal subspaces, which is Cochran's theorem in
  projection form. Missing are the identification of the fitted values and
  residuals of a least-squares fit with such projections, the evaluation
  of the supremum by Cauchy–Schwarz, and the coverage statement; with the
  projection theorems these form a short argument.

### Comparison of experiments

Experiment $\mathcal E$ is **more informative** than $\mathcal F$ when every
procedure based on $\mathcal F$, for every decision problem, is matched by
one based on $\mathcal E$ with risk no larger at every parameter value.

* **101.62. Blackwell's theorem.** Let $\mathcal E=\{P_\theta\}$ and
  $\mathcal F=\{Q_\theta\}$ be dominated experiments with the same finite
  parameter space, the sample space of $\mathcal F$ standard Borel. The
  following are equivalent: $\mathcal E$ is more informative than
  $\mathcal F$; there is a Markov kernel $K$ with
  $Q_\theta=\int K(x,\cdot)\,P_\theta(dx)$ for every $\theta$; for every
  finite action space and bounded loss, every risk function available from
  $\mathcal F$ is available from $\mathcal E$. Mathlib proves that a
  garbling cannot decrease Bayes or minimax risk. Statlib adds that
  forgetting a component of the observation cannot decrease the Bayes
  risk, a decomposition of DeGroot's statistical information along a
  garbling, data processing for the binary Bayes risk and the statistical
  information, and the invariance of every $f$-divergence under a kernel
  with a Markov left inverse. Missing are the pointwise risk-function form
  and the converse from risk comparison to the existence of a garbling,
  which needs a separation argument in the space of risk functions.

### Further bounds, shrinkage, and simultaneous testing

* **101.64. Stein's identity and unbiased risk estimation.** Let
  $X\sim N_p(\theta,\sigma^2I)$ with known $\sigma^2>0$. For weakly
  differentiable $g:\mathbb R^p\to\mathbb R^p$ with
  $\mathbb E\|g(X)\|^2<\infty$ and
  $\mathbb E|\partial_ig_i(X)|<\infty$,
  $$\mathbb E[(X_i-\theta_i)g_i(X)]=\sigma^2\,\mathbb E\,\partial_ig_i(X),$$
  so the squared-error risk of $X+g(X)$ is the expectation of
  $p\sigma^2+\|g(X)\|^2+2\sigma^2\sum_i\partial_ig_i(X)$. TauCeti proves
  the identity in dimension one: for $X\sim N(\mu,v)$, $v\ge0$, and $f$
  differentiable everywhere with $(x-\mu)f(x)$ and $f'$ integrable,
  $\mathbb E[(X-\mu)f(X)]=v\,\mathbb Ef'(X)$. Missing are the
  $p$-dimensional form for weakly differentiable $g$ and the unbiased risk
  estimate.

### Likelihood and convex geometry

* **101.69. Existence of an exponential-family maximum.** In a minimal
  regular natural exponential family with cumulant $A$, the log-likelihood
  of an independent sample is $n(\eta\cdot\bar T-A(\eta))$ up to a
  constant. It has a maximizer over the open natural parameter space if
  and only if $\bar T$ lies in the interior $K^\circ$ of the convex hull of
  the support of $T$; the maximizer is then unique and solves
  $\nabla A(\hat\eta)=\bar T$. Absent; it depends on the mean-value
  diffeomorphism of 101.42, which is itself missing.

## 102. Asymptotic, semiparametric, and robust statistics

None of the three libraries contains statistical asymptotics: there is no
statistical model indexed by a parameter and a sample size, no estimator
sequence, Fisher information, influence function, delta method, local
asymptotic normality, Le Cam lemma, Edgeworth expansion, or bootstrap
theorem. Statlib defines contiguity, in five formulations of which two
elementary relations are proved, and differentiability in quadratic mean,
with the mean-zero property of the score; it also proves the weak law of
large numbers in Banach spaces. Mathlib supplies the probabilistic
infrastructure: convergence in distribution across varying probability
spaces with Slutsky's theorem and continuous mapping, the central limit
theorem for independent identically distributed real variables, the
Cramér–Wold device, multivariate Gaussian laws, Kullback–Leibler
divergence and log-likelihood ratios, exponential tilting, conditional
expectation as an $L^2$ projection with the law of total variance, Taylor
expansions of characteristic functions, the Lévy–Prokhorov metric, Sion's
theorem, and Riemannian manifolds. TauCeti adds quantile functions and
exact laws of order statistics, chi-squared laws of Gaussian sums of
squares and of orthogonal projections of a standard Gaussian, the
noncentral chi-squared law, the moment generating function of Gaussian
quadratic forms, affine images of multivariate Gaussians, the multinomial
covariance, Fourier inversion for laws with integrable characteristic
function, characterizations of weak convergence by distribution functions
and by bounded Lipschitz test functions, Lindeberg's replacement
inequality, the Hermite basis of $L^2(\gamma)$, the
sampling-with-replacement law, and one genuine consistency theorem, for
empirical Fréchet barycenters. Only that consistency result and the
unconditional half of the multiple-imputation identities are partial
coverage. Missing is essentially the whole section: the delta methods,
likelihood and $M$-estimation asymptotics, $U$-statistics, Le Cam's theory
of local asymptotic normality and limits of experiments, Pitman efficiency,
semiparametric efficiency, robust minimax theory, Edgeworth and
saddlepoint expansions, bootstrap consistency and accuracy, and Čencov's
characterization of the Fisher metric. The multivariate central limit
theorem, a prerequisite for most vector statements, is not stated, although
it follows directly from the Cramér–Wold device and the one-dimensional
theorem.

Sources: [mathematical synopsis](SYNOPSIS102.md); [combined coverage inventory](STRUCTURE102.md).

Observations $X_1,\ldots,X_n$ are independent with common law $P_\theta$, or
$P$, unless stated otherwise; $P_n$ is the empirical measure, $F_n$ the
empirical distribution function, $\ell_n$ the log-likelihood, and
$I(\theta)$ the Fisher information matrix of one observation. Write
$\Rightarrow$ for convergence in distribution, $\to_P$ for convergence in
probability, and $o_P(1)$, $O_P(1)$ for sequences converging to zero in
probability and uniformly tight sequences. A dominated model with densities
$p_\theta$ is **differentiable in quadratic mean** (DQM) at $\theta$ with
score $\dot\ell_\theta\in L^2(P_\theta)$ when
$$\int\Bigl(\sqrt{p_{\theta+h}}-\sqrt{p_\theta}
-\tfrac12h^\top\dot\ell_\theta\sqrt{p_\theta}\Bigr)^2d\mu=o(\|h\|^2).$$
Write $\Phi$ and $\varphi$ for the standard normal distribution function and
density and $z_\alpha$ for the upper $\alpha$-quantile.

### Parametric estimators and tests

* **102.1. Delta method.** If $\sqrt n(T_n-\theta)\Rightarrow N(0,\Sigma)$
  in $\mathbb R^k$ and $g:\mathbb R^k\to\mathbb R^m$ is Borel measurable and
  differentiable at $\theta$, then
  $$\sqrt n\bigl(g(T_n)-g(\theta)\bigr)\Rightarrow
  N\bigl(0,Dg(\theta)\Sigma Dg(\theta)^\top\bigr),$$
  and $\sqrt n(g(T_n)-g(\theta))-Dg(\theta)\sqrt n(T_n-\theta)\to_P0$.
  Mathlib has Slutsky's theorem, continuous mapping, transfer of limits
  under $o_P(1)$ perturbations and Fréchet derivatives with little-$o$
  remainder; TauCeti computes affine images of multivariate Gaussians. The
  theorem follows by a short argument once the lemma that a deterministic
  $o(\|h\|)$ remainder evaluated along an $O_P(n^{-1/2})$ sequence is
  $o_P(n^{-1/2})$ is supplied, but no library has that lemma or stochastic
  order symbols.

* **102.2. Consistency of maximum likelihood.** Let $\Theta$ be a compact
  metric space, the model dominated and identifiable, and
  $\theta\mapsto\log p_\theta(x)$ upper semicontinuous for almost every
  $x$. Suppose every point of $\Theta$ has an open ball $U$ for which
  $\sup_{\theta\in U}\log(p_\theta/p_{\theta_0})$ is measurable with
  $\mathbb E_{\theta_0}\sup_{\theta\in U}\log(p_\theta/p_{\theta_0})(X)
  <\infty$. If $\ell_n(\hat\theta_n)\ge\ell_n(\theta_0)-o_P(n)$ under
  $P_{\theta_0}$, then $\hat\theta_n\to\theta_0$ in
  $P_{\theta_0}$-probability. Gibbs' inequality for Kullback–Leibler
  divergence, which drives Wald's argument, is in Mathlib; parametric
  families and maximum likelihood are not defined.

* **102.3. Asymptotic normality of maximum likelihood.** Let $\Theta$ be
  open in $\mathbb R^k$; assume that $\vartheta\mapsto\log p_\vartheta(x)$
  is three times continuously differentiable near $\theta$ for every $x$,
  with third partial derivatives dominated by a $P_\theta$-integrable
  function, that the score has mean zero and finite nonsingular covariance
  $I(\theta)$, and that $\mathbb E_\theta D^2\log p_\theta=-I(\theta)$. A
  consistent root $\hat\theta_n$ of the likelihood equation satisfies
  $$\sqrt n(\hat\theta_n-\theta)=I(\theta)^{-1}n^{-1/2}
  \sum_{i=1}^n\dot\ell_\theta(X_i)+o_P(1)\Rightarrow N(0,I(\theta)^{-1}),$$
  and a consistent sequence of maximizers is such a root with probability
  tending to one. Not present; it needs the multivariate central limit
  theorem and a theory of parametric densities.

* **102.4. Z-estimators.** Let $\Theta$ be open in $\mathbb R^k$,
  $\psi_\theta(x)\in\mathbb R^k$, $\Psi(\theta)=\mathbb E_{\theta_0}
  \psi_\theta(X)$ with $\Psi(\theta_0)=0$ and
  $\mathbb E_{\theta_0}\|\psi_{\theta_0}\|^2<\infty$, and suppose
  $\|\psi_{\theta_1}(x)-\psi_{\theta_2}(x)\|\le\dot\psi(x)
  \|\theta_1-\theta_2\|$ near $\theta_0$ with
  $\mathbb E_{\theta_0}\dot\psi^2<\infty$. If $\Psi$ is differentiable at
  $\theta_0$ with nonsingular derivative $V$ and $\hat\theta_n$ is
  consistent with $n^{-1}\sum_i\psi_{\hat\theta_n}(X_i)=o_P(n^{-1/2})$, then
  $$\sqrt n(\hat\theta_n-\theta_0)=-V^{-1}n^{-1/2}\sum_{i=1}^n
  \psi_{\theta_0}(X_i)+o_P(1)\Rightarrow N\bigl(0,V^{-1}\Sigma V^{-\top}\bigr),$$
  with $\Sigma$ the covariance of $\psi_{\theta_0}(X)$. Absent from all
  three libraries.

* **102.6. Sample quantiles.** If $0<p<1$, $F$ is strictly increasing
  near $q=F^{-1}(p)$ and differentiable there with $f(q)>0$, then
  $$\sqrt n\bigl(F_n^{-1}(p)-q\bigr)\Rightarrow N\bigl(0,p(1-p)/f(q)^2\bigr).$$
  TauCeti has the quantile function with its Galois characterization and
  the exact laws of order statistics as quantile images of beta laws; no
  limit theorem for them is proved.

* **102.7. Bahadur representation of sample quantiles.** Let $0<p<1$,
  $F_n^{-1}(p)=\inf\{x:F_n(x)\ge p\}$, and $F$ differentiable at
  $\xi_p=F^{-1}(p)$ with $f(\xi_p)>0$. Then
  $$F_n^{-1}(p)=\xi_p+\frac{p-F_n(\xi_p)}{f(\xi_p)}+R_n,\qquad
  \sqrt nR_n\to_P0,$$
  so finitely many sample quantiles are jointly asymptotically normal with
  covariance $(p\wedge p'-pp')/(f(\xi_p)f(\xi_{p'}))$. If $F$ is twice
  differentiable at $\xi_p$, the Bahadur–Kiefer theorem gives
  $$\limsup_n\frac{n^{3/4}|R_n|}{(\log\log n)^{3/4}}
  =\frac{(32p(1-p)/27)^{1/4}}{f(\xi_p)}\quad\text{almost surely}.$$
  Absent; the empirical distribution function is not defined in any of
  the three libraries.

* **102.8. Nondegenerate $U$-statistics.** Let $h$ be a symmetric kernel
  of order $m$ with $\mathbb Eh(X_1,\ldots,X_m)^2<\infty$, $U_n$ its
  average over the $\binom nm$ subsamples, $\theta=\mathbb Eh$, and
  $g(x)=\mathbb Eh(x,X_2,\ldots,X_m)-\theta$. If
  $\zeta_1=\mathop{\mathrm{Var}}g(X_1)>0$, then
  $\sqrt n(U_n-\theta)\Rightarrow N(0,m^2\zeta_1)$, and
  $\sqrt n(U_n-\theta-n^{-1}\sum_img(X_i))\to0$ in $L^2$. Mathlib's $L^2$
  conditional expectation supplies the projection operation; $U$-statistics
  are not defined.

* **102.11. Likelihood-ratio, Wald, and score tests.** Let $\Theta$ be
  open in $\mathbb R^k$ and $\Theta_0=\{c(\theta)=0\}$ for a continuously
  differentiable $c:\Theta\to\mathbb R^q$ whose derivative $C$ at
  $\theta_0\in\Theta_0$ has rank $q$. Under the hypotheses of 102.3 at
  $\theta_0$, with $I$ continuous there, and for consistent maximizers
  $\hat\theta_n$ over $\Theta$ and $\tilde\theta_n$ over $\Theta_0$, the
  statistics
  $\lambda_n=2(\ell_n(\hat\theta_n)-\ell_n(\tilde\theta_n))$,
  $$W_n=n\,c(\hat\theta_n)^\top\bigl[Dc(\hat\theta_n)I(\hat\theta_n)^{-1}
  Dc(\hat\theta_n)^\top\bigr]^{-1}c(\hat\theta_n),\qquad
  S_n=\tfrac1n\nabla\ell_n(\tilde\theta_n)^\top I(\tilde\theta_n)^{-1}
  \nabla\ell_n(\tilde\theta_n)$$
  each converge to $\chi^2_q$ under $P_{\theta_0}$ and differ by $o_P(1)$.
  If the model is DQM at $\theta_0$, then under $P_{\theta_0+h/\sqrt n}$
  the common limit is noncentral $\chi^2_q$ with noncentrality
  $(Ch)^\top[CI(\theta_0)^{-1}C^\top]^{-1}Ch$. TauCeti has the limit laws:
  the chi-squared law of sums of squared independent Gaussians and of the
  squared norm of a standard Gaussian projected onto a subspace, and the
  noncentral chi-squared law of $\|X\|^2$ for $X\sim N(m,I_q)$, with
  noncentrality $\|m\|^2$. The chi-squared law of $Z^\top\Sigma^{-1}Z$ for
  $Z\sim N(0,\Sigma)$, a short consequence, and the asymptotic statements
  are absent.

### Limits of experiments

A sequence $Q_n$ is **contiguous** to $P_n$ when $P_n(A_n)\to0$ implies
$Q_n(A_n)\to0$. The experiments are **locally asymptotically normal**
(LAN) at $\theta$ with nonsingular information $I(\theta)$ and central
sequence $\Delta_n$ when
$\log(dP^n_{\theta+h/\sqrt n}/dP^n_\theta)=h\cdot\Delta_n
-\tfrac12h^\top I(\theta)h+o_{P_\theta}(1)$ for every $h$ and
$\Delta_n\Rightarrow N(0,I(\theta))$. An estimator sequence is **regular**
at $\theta$ when the law of $\sqrt n(T_n-\theta-h/\sqrt n)$ under
$P_{\theta+h/\sqrt n}$ has a limit independent of $h$.

* **102.12. Contiguity.** If the likelihood ratio $L_n=dQ_n^{\mathrm a}/dP_n$
  of the part of $Q_n$ absolutely continuous with respect to $P_n$
  converges in distribution under $P_n$ to $e^\Lambda$ for a real random
  variable $\Lambda$ with $\mathbb Ee^\Lambda=1$, then $Q_n$ is contiguous to $P_n$; in
  particular local alternatives in a LAN experiment are mutually
  contiguous. Mathlib has absolute continuity, Radon–Nikodým derivatives,
  the Lebesgue decomposition and log-likelihood ratios. Statlib defines
  contiguity for families of probability measures indexed along a filter,
  in five formulations, among them the one above and the condition that
  weak limits of the laws of $dQ_n/dP_n$ under $P_n$ have mean one. It
  proves only that the set formulation, tested along every finer filter,
  is equivalent to preservation of convergence in probability and implies
  the set formulation along the filter itself. The
  likelihood-ratio characterizations, which contain this statement, appear
  there only as plans in comments. With the definition in place the
  statement follows by a short argument.

* **102.13. Local asymptotic normality of smooth models.** For independent
  sampling from a model that is DQM at an interior point $\theta$ with
  nonsingular $I(\theta)=\mathbb E_\theta\dot\ell_\theta
  \dot\ell_\theta^\top$, the product experiments are LAN with central
  sequence $\Delta_n=n^{-1/2}\sum_i\dot\ell_\theta(X_i)$. Suppose in
  addition that the densities $p_{\theta+h}$ for $h$ near $0$ are positive
  on a common set $A$ and vanish outside it, and that for $x\in A$ the maps
  $h\mapsto p_{\theta+h}(x)$ and
  $h\mapsto p_{\theta+h}(x)\log(p_{\theta+h}(x)/p_\theta(x))$ are twice
  continuously differentiable near $0$, with first and second derivatives
  bounded in absolute value, for $h$ in a neighborhood of $0$, by a
  $\mu$-integrable function of $x$. Then
  $D(P_{\theta+h}\|P_\theta)=\tfrac12h^\top I(\theta)h+o(\|h\|^2)$.
  Statlib defines differentiability in quadratic mean, with a linear score
  map into $L^2(P_\theta)$ as in the definition above, proves that the
  score has mean zero at an interior point, and defines the squared
  Hellinger distance, with the normalization
  $\tfrac12\int(\sqrt p-\sqrt q)^2$. TauCeti proves the pointwise comparison of the Hellinger and
  relative-entropy integrands, a supporting inequality. Local asymptotic
  normality and the divergence expansion are absent.

* **102.14. Le Cam's third lemma.** If under $P_n$ the pair
  $(S_n,\Lambda_n)$ converges to a normal law whose second margin is
  $N(-\sigma^2/2,\sigma^2)$ and whose cross-covariance is $\tau$, and
  $\Lambda_n$ is the log-likelihood ratio of $Q_n$ against $P_n$, then
  under $Q_n$ the sequence $S_n$ converges to the normal law with the same
  covariance and mean shifted by $\tau$. TauCeti proves that tilting
  $N(m,v)$ by $e^{tx}$ gives $N(m+vt,v)$, the one-dimensional computation
  in the limit; the bivariate statement and the passage to the limit are
  missing, and Statlib's definitions of contiguity carry no change-of-law
  theorem.

* **102.15. Asymptotic representation theorem.** Let the model be DQM at
  an interior $\theta$ with nonsingular $I(\theta)$, and let $T_n$
  converge in distribution under $P^n_{\theta+h/\sqrt n}$ to $L_h$ for
  every $h\in\mathbb R^k$. Then there is a randomized statistic $T(X,U)$
  in the Gaussian shift experiment $X\sim N(h,I(\theta)^{-1})$, with $U$
  uniform and independent of $X$, such that $T$ has law $L_h$ for every
  $h$. TauCeti represents every law on a standard Borel space as the image
  of a uniform variable, the construction of randomized statistics; the
  theorem needs Le Cam's weak convergence of experiments, which is absent.

* **102.16. Convolution theorem.** In a LAN experiment with information
  $I(\theta)$, the limit law of a regular estimator sequence is the
  convolution of $N(0,I(\theta)^{-1})$ with some probability measure; if
  it has finite covariance, that covariance is at least $I(\theta)^{-1}$
  in the Loewner order. An estimator with
  $\sqrt n(T_n-\theta)=I(\theta)^{-1}\Delta_n+o_{P_\theta}(1)$ is regular
  with limit $N(0,I(\theta)^{-1})$. Absent from all three libraries.

* **102.17. Local asymptotic minimax theorem.** Let $\ell\ge0$ be lower
  semicontinuous with convex sublevel sets symmetric about zero. For every
  estimator sequence in a LAN experiment,
  $$\lim_{c\to\infty}\liminf_{n\to\infty}\sup_{\|h\|\le c}
  \mathbb E_{\theta+h/\sqrt n}\ell\bigl(\sqrt n(T_n-\theta-h/\sqrt n)\bigr)
  \ge\int\ell\,dN(0,I(\theta)^{-1}),$$
  with equality for every bounded continuous such $\ell$ when the
  experiments are those of 102.13 and
  $\sqrt n(T_n-\theta)=I(\theta)^{-1}\Delta_n+o_{P_\theta}(1)$. Mathlib's
  minimax risk is a finite-sample notion; Anderson's lemma, which would
  build on TauCeti's Brunn–Minkowski and Prékopa–Leindler inequalities,
  and the asymptotic bound are absent.

### Local tests and asymptotic relative efficiency

Given $0<\alpha<\gamma<1$ and alternatives $\theta_\nu\downarrow0$ for
$H_0:\theta=0$, let $n_{\nu,i}$ be the least sample size at which the
$i$th sequence of tests has level at most $\alpha$ and power at least
$\gamma$ at $\theta_\nu$; the **Pitman efficiency** is
$\lim_\nu n_{\nu,2}/n_{\nu,1}$. Statistics $T_n$ are **locally uniformly
asymptotically normal** with functions $\mu,\sigma$ when
$\sqrt n(T_n-\mu(\theta_n))/\sigma(\theta_n)\Rightarrow N(0,1)$ under every
$\theta_n\downarrow0$; the **efficacy** is $(\mu'(0)/\sigma(0))^2$.

* **102.21. Pitman efficiency and Noether's theorem.** Suppose
  $P_{n,\theta}\to P_{n,0}$ in total variation as $\theta\to0$ for each
  $n$, and let $T_{n,1},T_{n,2}$ be locally uniformly asymptotically
  normal with $\mu_i$ differentiable at $0$, $\mu_i'(0)>0$, and
  $\sigma_i$ continuous at $0$ with $\sigma_i(0)>0$. The tests rejecting when
  $\sqrt n(T_{n,i}-\mu_i(0))>\sigma_i(0)z_\alpha$ have asymptotic level
  $\alpha$ and local power
  $1-\Phi(z_\alpha-h\mu_i'(0)/\sigma_i(0))$ at $h/\sqrt n$, and their
  Pitman efficiency is the ratio of efficacies, for every $\alpha$,
  $\gamma$ and $\theta_\nu\downarrow0$. TauCeti supplies $\Phi$ and its
  quantiles; tests, power functions and relative efficiency are not
  defined.

### General criteria, moment methods, and nonlinear limits

* **102.23. Consistency of $M$-estimators.** Suppose
  $\sup_\theta|P_nm_\theta-Pm_\theta|\to_P0$ and
  $\sup_{d(\theta,\theta_0)\ge\varepsilon}Pm_\theta<Pm_{\theta_0}$ for
  every $\varepsilon>0$. If
  $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(1)$, then
  $\hat\theta_n\to_P\theta_0$. The uniform convergence holds when $\Theta$
  is a compact metric space, $\theta\mapsto m_\theta(x)$ is continuous, and
  $P\sup_\theta|m_\theta|<\infty$. TauCeti proves almost-sure consistency
  of empirical Fréchet barycenters in separable metric spaces, an
  $M$-estimator with criterion $-d(\theta,x)^p$, by way of Wasserstein
  convergence of empirical measures. Missing are the general criterion and
  the uniform law of large numbers over a compact parameter set.

* **102.24. Asymptotic normality of $M$-estimators.** Let $\Theta$ be
  open in $\mathbb R^k$, $\theta\mapsto m_\theta(x)$ differentiable at
  $\theta_0$ for almost every $x$ with derivative $\dot m_{\theta_0}$, and
  $|m_{\theta_1}-m_{\theta_2}|\le\dot m\|\theta_1-\theta_2\|$ near
  $\theta_0$ with $P\dot m^2<\infty$. Suppose $\theta\mapsto Pm_\theta$ has
  a second-order Taylor expansion at its maximum $\theta_0$ with
  nonsingular symmetric second derivative $V$. If
  $P_nm_{\hat\theta_n}\ge\sup_\theta P_nm_\theta-o_P(n^{-1})$ and
  $\hat\theta_n\to_P\theta_0$, then
  $$\sqrt n(\hat\theta_n-\theta_0)=-V^{-1}n^{-1/2}\sum_{i=1}^n
  \dot m_{\theta_0}(X_i)+o_P(1)\Rightarrow
  N\bigl(0,V^{-1}P[\dot m_{\theta_0}\dot m_{\theta_0}^\top]V^{-1}\bigr).$$
  Absent from all three libraries.

* **102.25. Rate of convergence of $M$-estimators.** Let $M_n$ be random
  criterion functions and $M$ a deterministic function on a semimetric
  space $(\Theta,d)$ with a point of maximum $\theta_0$, and write
  $\mathbb E^*$ for outer expectation. Suppose
  $M(\theta)-M(\theta_0)\le-c\,d(\theta,\theta_0)^2$ near $\theta_0$ with
  $c>0$, and that for every $n$ and all sufficiently small $\delta>0$
  $$\mathbb E^*\sup_{d(\theta,\theta_0)<\delta}
  |(M_n-M)(\theta)-(M_n-M)(\theta_0)|\le C\phi_n(\delta)/\sqrt n,$$
  where $C\ge0$ does not depend on $n$ or $\delta$ and
  $\delta\mapsto\phi_n(\delta)/\delta^a$ is decreasing for some $a<2$ not
  depending on $n$. If $r_n^2\phi_n(1/r_n)\le\sqrt n$ for every $n$,
  $M_n(\hat\theta_n)\ge M_n(\theta_0)-O_P(r_n^{-2})$ and
  $\hat\theta_n\to\theta_0$ in outer probability, then
  $r_nd(\hat\theta_n,\theta_0)=O_P(1)$; the moduli $\delta$ and
  $\delta^{1/2}$ give the rates $\sqrt n$ and $n^{1/3}$. Outer expectations
  and the peeling argument are absent.

A map $\Phi$ between subsets of normed spaces is **Hadamard
differentiable** at $\theta$ tangentially to a linear space $D_0$ if there
is a continuous linear $\Phi'_\theta$ with
$[\Phi(\theta+t_nh_n)-\Phi(\theta)]/t_n\to\Phi'_\theta h$ whenever
$t_n\downarrow0$, $h_n\to h\in D_0$, and the arguments lie in the domain.

* **102.28. Functional delta method.** If
  $r_n(T_n-\theta)\Rightarrow G$ in a normed space, $r_n\to\infty$, $G$ is
  tight and supported on a linear subspace $D_0$, and $\Phi$ is Hadamard
  differentiable at $\theta$ tangentially to $D_0$, then
  $r_n(\Phi(T_n)-\Phi(\theta))\Rightarrow\Phi'_\theta G$. Hadamard
  differentiability and weak convergence of non-measurable maps in
  $\ell^\infty$ are not present in any of the three libraries.

* **102.29. Hoeffding decomposition.** For the square-integrable symmetric
  kernel of 102.8 there are symmetric canonical kernels $h_j$,
  $1\le j\le m$, with zero conditional expectation in each argument, such
  that, with $U_{n,j}$ the $U$-statistic of $h_j$,
  $$U_n-\theta=\sum_{j=1}^m\binom mjU_{n,j},\qquad
  \mathop{\mathrm{Var}}U_n=\sum_{j=1}^m\binom mj^2\binom nj^{-1}
  \mathbb Eh_j^2,$$
  the terms being orthogonal in $L^2$ and $h_1=g$. Among estimators
  unbiased for $\mathbb E_Ph$ with finite variance at every $P$ with
  $\mathbb E_Ph^2<\infty$, $U_n$ has the smallest variance. Symmetric
  kernels on product spaces and the decomposition are absent.

* **102.30. Degenerate quadratic $U$-statistics.** Let $h\in
  L^2(P\otimes P)$ be symmetric with $\mathbb E[h(X_1,X_2)\mid X_1]=0$, and
  let $(\lambda_j)$ be the eigenvalues of the integral operator with
  kernel $h$ on $L^2(P)$. Then $nU_n\Rightarrow\sum_j\lambda_j(Z_j^2-1)$
  for independent standard normal $Z_j$, the series converging in $L^2$.
  Absent; it needs in addition the spectral expansion of a symmetric
  Hilbert–Schmidt kernel in $L^2(P\otimes P)$ and the limit of the
  resulting Gaussian chaos.

* **102.31. Pearson's multinomial tests.** If
  $(N_1,\ldots,N_k)\sim\mathop{\mathrm{Mult}}(n;p)$ with fixed $k$ and all
  $p_i>0$, then $\sum_i(N_i-np_i)^2/(np_i)\Rightarrow\chi^2_{k-1}$. Let
  $p=p(\vartheta_0)$ for a map $\vartheta\mapsto p(\vartheta)$ from an
  open set in $\mathbb R^d$ into the open simplex that is continuously
  differentiable with derivative of rank $d$ at $\vartheta_0$. If
  $\hat\vartheta_n$ is a consistent maximum likelihood estimator of
  $\vartheta_0$, the statistic with $p(\hat\vartheta_n)$ in place of $p$
  converges to $\chi^2_{k-1-d}$. For an $r\times c$ table under
  independence, fitted counts $\hat N_{ij}=N_{i+}N_{+j}/n$ give
  $(r-1)(c-1)$ degrees of freedom, and the likelihood-ratio statistic
  $2\sum N_{ij}\log(N_{ij}/\hat N_{ij})$, with $0\log0=0$, has the same
  limit and differs from Pearson's by $o_P(1)$.
  TauCeti computes the multinomial covariance and proves the chi-squared
  law of the squared norm of a standard Gaussian vector after an
  orthogonal projection of rank $k-1$. The simple-hypothesis case follows
  by a short argument from these and the multivariate central limit
  theorem, which is not stated but follows from Mathlib's Cramér–Wold
  device and one-dimensional central limit theorem; the composite case
  needs 102.3.

* **102.33. Argmax theorem.** Let $M_n,M$ be processes indexed by a
  metric space $H$ with $M_n\Rightarrow M$ in $\ell^\infty(K)$ for every
  compact $K\subset H$, and let almost every path of $M$ be upper
  semicontinuous with a unique maximizer $T$, a tight random element. If
  $T_n$ is uniformly tight and $M_n(T_n)\ge\sup_hM_n(h)-o_P(1)$, then
  $T_n\Rightarrow T$. The space $\ell^\infty(K)$ with its weak convergence
  is not available, and the theorem is absent.

### Semiparametric models and missing data

In a **semiparametric model** $\{P_{\theta,\eta}\}$ with Euclidean $\theta$
and infinite-dimensional $\eta$, the **nuisance tangent space** is the
closed linear span of the scores of smooth submodels varying only $\eta$;
the **efficient score** $\tilde\ell_\theta$ is the residual of the score
for $\theta$ after projection onto it, and the **efficient information** is
$\tilde I(\theta)=\mathbb E\tilde\ell_\theta\tilde\ell_\theta^\top$.

* **102.34. Semiparametric convolution bound.** Fix
  $P=P_{\theta,\eta}$, and suppose the submodels below have densities
  relative to a common $\sigma$-finite measure. Suppose that for every
  $a\in\mathbb R^k$ and every
  nuisance submodel $\eta_t$ in a given class, $t\mapsto
  P_{\theta+ta,\eta_t}$ is DQM at $0$ with score $a^\top\dot\ell_\theta+g$,
  the nuisance scores $g$ forming a linear space whose closure is the
  nuisance tangent space, and that $\tilde I(\theta)$ is nonsingular. Then
  the limit law of every estimator sequence regular along all such
  submodels is the convolution of $N(0,\tilde I(\theta)^{-1})$ with a
  probability measure, and an estimator is regular with limit
  $N(0,\tilde I(\theta)^{-1})$ if and only if
  $\sqrt n(T_n-\theta)=n^{-1/2}\sum_i\tilde I(\theta)^{-1}
  \tilde\ell_\theta(X_i)+o_P(1)$. Mathlib's orthogonal projection with its
  Pythagorean identity is the defining operation; tangent spaces and the
  theorem are absent.

### Pathwise derivatives and orthogonal estimation

Let $Y$ be a response, $X$ always-observed covariates, and $R$ the
indicator that $Y$ is observed; the observations are copies of $(R,X,RY)$
and the response is missing at random, $P(R=1\mid X,Y)=\pi_0(X)$. Write
$m_0(x)=\mathbb E[Y\mid X=x]$, $\mu=\mathbb EY$, and
$\varphi_{m,\pi}=RY/\pi(X)-(R-\pi(X))m(X)/\pi(X)$.

* **102.39. Cross-fitted estimation of a missing mean.** Split the sample
  into a fixed number of folds, with every fold of size at least $cn$
  for some $c>0$ and all sufficiently large $n$. Evaluate
  $\varphi_{\hat m,\hat\pi}$ on each fold with nuisance estimates from the
  other folds, and let $\hat\mu$ be the overall average. Suppose $Y\in
  L^2$, the true and fitted response probabilities are bounded below by
  $\delta>0$, and on each fold, in $L^2$ of the law of $X$,
  $\|\hat m-m_0\|_2\to_P0$, $\|\hat\pi-\pi_0\|_2\to_P0$,
  $\|\hat m-m_0\|_2\|\hat\pi-\pi_0\|_2=o_P(n^{-1/2})$, and
  $\|\varphi_{\hat m,\hat\pi}-\varphi_{m_0,\pi_0}\|_{L^2(P)}\to_P0$ with the
  nuisance estimates held fixed. Then
  $$\sqrt n(\hat\mu-\mu)=n^{-1/2}\sum_{i=1}^n\Bigl[m_0(X_i)
  +\frac{R_i(Y_i-m_0(X_i))}{\pi_0(X_i)}-\mu\Bigr]+o_P(1),$$
  whose summand is the efficient influence function. Mathlib's tower and
  pull-out properties give the double-robustness computation behind it;
  the cross-fitting theorem is absent.

### Adaptation, missing information, and multiple imputation

* **102.41. Adaptive estimation of a center of symmetry.** Let the
  observations have density $\eta(x-\theta)$, with $\eta$ ranging over all
  densities symmetric about zero that are absolutely continuous with
  finite Fisher information $I_\eta=\int(\eta'/\eta)^2\eta$. The efficient
  score is the ordinary location score and the efficient information is
  $I_\eta$, and there are estimators $\hat\theta_n$, not depending on
  $\eta$, with $\sqrt n(\hat\theta_n-\theta)\Rightarrow N(0,I_\eta^{-1})$
  regularly at every such $\eta$. Absent from all three libraries.

### Robust statistics

The **influence function** of a functional $T$ at $F$ is
$\mathop{\mathrm{IF}}(x;T,F)=\lim_{\varepsilon\downarrow0}
[T((1-\varepsilon)F+\varepsilon\delta_x)-T(F)]/\varepsilon$, and
$\psi_k(u)=\max(-k,\min(k,u))$ is the Huber score.

* **102.44. $M$-estimators and the Huber minimax property.** For odd
  continuous $\psi$, let $T$ be the location $M$-functional defined, on a
  set of laws containing the contaminations
  $(1-\varepsilon)F+\varepsilon\delta_x$, by $\int\psi(x-T(G))\,dG(x)=0$,
  with $\theta_0=T(F)$,
  $\lambda(\theta)=\int\psi(x-\theta)\,dF$ differentiable at $\theta_0$
  with $\gamma=-\lambda'(\theta_0)\ne0$, and
  $\varepsilon\mapsto T((1-\varepsilon)F+\varepsilon\delta_x)$
  differentiable at $0$, $\mathop{\mathrm{IF}}(x;T,F)=\psi(x-\theta_0)/
  \gamma$. If moreover $\psi$ is Lipschitz and
  $\mathbb E\psi(X-\theta_0)^2<\infty$, a consistent sequence
  $\hat\theta_n$ with $\sum_i\psi(X_i-\hat\theta_n)=o_P(n^{1/2})$
  satisfies
  $\sqrt n(\hat\theta_n-\theta_0)\Rightarrow
  N(0,\mathbb E\psi(X-\theta_0)^2/\gamma^2)$. Hampel's optimality: for
  $c>\sqrt{\pi/2}$, among $\phi$ with $\int\phi\,d\Phi=0$,
  $\int x\phi\,d\Phi=1$ and $\sup|\phi|\le c$, the integral
  $\int\phi^2d\Phi$ is uniquely minimized by $\psi_k/(2\Phi(k)-1)$ with
  $k/(2\Phi(k)-1)=c$. Huber's minimax property: for $0<\varepsilon<1$ let
  $k$ solve $2\varphi(k)/k-2\Phi(-k)=\varepsilon/(1-\varepsilon)$ and let
  $G_0$ have density $(1-\varepsilon)\varphi(x)$ for $|x|\le k$ and
  $(1-\varepsilon)\varphi(k)e^{k^2-k|x|}$ for $|x|>k$. Then
  $G_0=(1-\varepsilon)\Phi+\varepsilon H_0$ with $H_0$ symmetric,
  $\psi_k=-g_0'/g_0$, and with
  $V(\psi_k,G)=\int\psi_k^2\,dG/G((-k,k))^2$,
  $$V(\psi_k,G)\le V(\psi_k,G_0)=1/I(G_0)$$
  for every $G=(1-\varepsilon)\Phi+\varepsilon H$ with symmetric $H$, while
  $\int\psi^2dG_0/(\int\psi'dG_0)^2\ge1/I(G_0)$ for every bounded
  absolutely continuous $\psi$ with $\int\psi'dG_0\ne0$. TauCeti supplies
  $\Phi$ and $\varphi$ as real functions; influence functions and the
  variance functional are not defined, and Mathlib's Sion theorem does not
  apply directly to Huber's saddle point.

### Von Mises expansions and regression $M$-estimators

* **102.48. Asymptotics of regression $M$-estimators.** In the linear
  model $Y_i=x_i^\top\beta+\varepsilon_i$ with fixed design rows (first
  coordinate one) and independent errors, let $\rho$ be convex with right
  derivative $\psi$, $n^{-1}\sum_ix_ix_i^\top\to Q$ positive definite and
  $\max_{i\le n}\|x_i\|/\sqrt n\to0$. Assume $\mathbb E\psi(\varepsilon)=0$,
  $\mathbb E\psi(\varepsilon)^2<\infty$,
  $\mathbb E(\psi(\varepsilon-t)-\psi(\varepsilon))^2\to0$ as $t\to0$, and
  $\gamma=-\tfrac d{dt}\mathbb E\psi(\varepsilon-t)|_{t=0}>0$. Then every
  sequence of minimizers of $\sum_i\rho(Y_i-x_i^\top t)$ satisfies
  $$\sqrt n(\hat\beta_n-\beta)=\frac{Q^{-1}}{\gamma\sqrt n}
  \sum_{i=1}^nx_i\psi(\varepsilon_i)+o_P(1)\Rightarrow
  N\Bigl(0,\frac{\mathbb E\psi(\varepsilon)^2}{\gamma^2}Q^{-1}\Bigr).$$
  Least squares is the case $\rho(u)=u^2/2$, with
  $\mathbb E\varepsilon^2<\infty$, and least absolute deviations the case
  $\rho(u)=|u|$ when $F$ has median $0$ and is differentiable there with
  $F'(0)>0$, so that $\gamma=2F'(0)$. Mathlib
  develops convex functions and one-sided derivatives, but no limit theorem
  for random convex processes; the statement is absent.

### Higher-order asymptotics, resampling, and information geometry

These entries open subdivision 102B and precede its first topic heading in
the synopsis.

* **102.49. One-term Edgeworth expansion.** For independent identically
  distributed nonlattice $X_i$ with mean $0$, variance $1$ and finite
  third moment $\rho=\mathbb EX_1^3$,
  $$P(\sqrt n\bar X\le x)=\Phi(x)-\varphi(x)(x^2-1)\frac{\rho}{6\sqrt n}
  +o(n^{-1/2})$$
  uniformly in $x$. Mathlib has the Taylor expansion of characteristic
  functions. TauCeti has the Hermite basis of $L^2(\gamma)$, Fourier
  inversion for laws with integrable characteristic function, and the
  identification of the frequencies at which a characteristic function
  equals one with the lattices carrying the law. Esseen's smoothing
  inequality and the Berry–Esseen theorem are absent.

* **102.50. Edgeworth expansion for smooth functions of means.** Let
  $X_i$ be independent copies of $X\in\mathbb R^d$ with mean $\mu$ and
  covariance $\Sigma$, let $j\ge1$, let $A$ have $j+2$ continuous
  derivatives near $\mu$ with $A(\mu)=0$ and
  $\sigma^2=\nabla A(\mu)^\top\Sigma\nabla A(\mu)>0$, and assume
  $\mathbb E\|X\|^{j+2}<\infty$ and Cramér's condition
  $\limsup_{\|t\|\to\infty}|\mathbb Ee^{it^\top X}|<1$. Then, uniformly in
  $x$,
  $$P\bigl(\sqrt nA(\bar X)/\sigma\le x\bigr)=\Phi(x)
  +\sum_{r=1}^jn^{-r/2}p_r(x)\varphi(x)+o(n^{-j/2}),$$
  with polynomials $p_r$ of degree at most $3r-1$, of parity opposite to
  $r$, whose coefficients are determined by the moments of $X$ of order at
  most $r+2$ and the derivatives of $A$ at $\mu$. Studentized statistics,
  including Student's $t$, are covered. Absent, for the reasons given at
  102.49.

* **102.51. Bootstrap of the mean.** For independent identically
  distributed real $X_i$ with finite variance $\sigma^2$, the Kolmogorov
  distance between the conditional law of $\sqrt n(\bar X^\star-\bar X)$
  given the sample and the law of $\sqrt n(\bar X-\mu)$ tends to zero in
  probability, and the conditional limit is $N(0,\sigma^2)$. TauCeti
  identifies the resampling law with independent draws from the empirical
  measure, characterizes weak convergence of laws on the line by
  convergence of distribution functions, and proves Lindeberg's
  replacement inequality for product measures with matching moments.
  Missing are conditional weak convergence in probability, a Kolmogorov
  distance, and the Lindeberg central limit theorem for triangular arrays
  on which the proof rests, of which the replacement inequality is the
  main step.

* **102.52. Bootstrap of the empirical distribution function.** For
  independent real observations with distribution function $F$, the
  conditional law of $\sqrt n(F_n^\star-F_n)$ converges in outer
  probability to the law of the $F$-Brownian bridge $B^0\circ F$ in the
  bounded Lipschitz metric on bounded functions with the supremum norm.
  No library has the empirical process, the Brownian bridge, or the
  bounded Lipschitz metric; TauCeti characterizes weak convergence of
  laws on a Polish space by uniform convergence over bounded Lipschitz
  test functions, without the metric, and gives the resampling law.

* **102.55. Saddlepoint approximation.** Let $K(s)=\log\mathbb Ee^{sX}$ be
  finite in an open neighborhood of the origin, let $\hat s$ solve
  $K'(\hat s)=x$ for $x$ in the interior of the range of $K'$ on the
  interior of the domain of $K$, and assume $X$ has a density and
  $\int|\mathbb Ee^{(\hat s+it)X}/\mathbb Ee^{\hat sX}|^\nu dt<\infty$ for
  some $\nu\ge1$. For $n>\nu$ the mean of $n$ independent copies has a
  continuous density $f_{\bar X}$, bounded if also
  $\int|\mathbb Ee^{itX}|^\nu dt<\infty$, and
  $$f_{\bar X}(x)=\Bigl(\frac n{2\pi K''(\hat s)}\Bigr)^{1/2}
  e^{n(K(\hat s)-\hat sx)}\bigl(1+O(n^{-1})\bigr).$$
  Mathlib proves that the tilted mean and variance are $K'$ and $K''$, and
  TauCeti computes the generating functions of tilted laws and proves
  Fourier inversion for laws with integrable characteristic function; the
  local limit theorem for densities and the expansion are absent.

* **102.58. Čencov's theorem.** On the open simplices $S_m$, $m\ge2$, with
  the Fisher–Rao metric $g_p(u,v)=\sum_iu_iv_i/p_i$ and the Amari–Chentsov
  tensor $T_p(u,v,w)=\sum_iu_iv_iw_i/p_i^2$ on tangent vectors
  ($\sum_iu_i=0$), let a **congruent embedding** $S_m\to S_n$,
  $2\le m\le n$, be $f(p)_j=p_iq^{(i)}_j$ for $j\in A_i$, given by a partition
  of $\{1,\ldots,n\}$ into nonempty blocks $A_1,\ldots,A_m$ and positive
  probability vectors $q^{(i)}$ on $A_i$. Every family of Riemannian
  metrics $h_m$ on the $S_m$ with $f^*h_n=h_m$ for all congruent
  embeddings is $c\,g$ for a constant $c>0$, and every invariant family of
  symmetric covariant $3$-tensors is a constant multiple of the
  Amari–Chentsov tensor. Mathlib has Riemannian manifolds in general; the
  Fisher–Rao metric, congruent embeddings and the theorem are absent.

### Accuracy and failure of the bootstrap

* **102.60. Second-order accuracy of the studentized bootstrap.** Let $X$ be a
  random vector in $\mathbb R^d$ with mean $\mu$, covariance $\Sigma$, and
  finite moments of every order. Assume Cramér's condition of 102.50 for
  the augmented vector $Z=(X,(X_jX_k)_{1\le j\le k\le d})$. Let $g$ be
  infinitely differentiable near $\mu$, with
  $\sigma^2=\nabla g(\mu)^\top\Sigma\nabla g(\mu)>0$. Put
  $$\hat\theta=g(\bar X),\qquad\theta=g(\mu),\qquad
  \hat\Sigma=\frac1n\sum_i(X_i-\bar X)(X_i-\bar X)^\top,\qquad
  \hat\sigma^2=\nabla g(\bar X)^\top\hat\Sigma\nabla g(\bar X).$$
  For a resample of size $n$, recompute the mean, covariance, and the
  entire variance estimate to obtain $\hat\theta^\star$ and
  $\hat\sigma^\star$. Define
  $T=\sqrt n(\hat\theta-\theta)/\hat\sigma$ and
  $T^\star=\sqrt n(\hat\theta^\star-\hat\theta)/\hat\sigma^\star$;
  use arbitrary finite definitions of the estimates outside the smooth
  neighborhood, and set the statistics to zero when their denominators
  vanish or their means lie outside that neighborhood. Under the joint
  sample-and-resample law these exceptional events have probability
  smaller than every fixed inverse power of $n$.
  Then
  $$\sup_x\bigl|P(T^\star\le x\mid X_1,\ldots,X_n)-P(T\le x)\bigr|
  =O_P(n^{-1}),$$
  whereas
  $$\sup_x|P(T\le x)-\Phi(x)|=n^{-1/2}\sup_x|p_1(x)\varphi(x)|+o(n^{-1/2}),$$
  with $p_1$ the polynomial of 102.50 applied to the smooth function of
  the augmented sample mean defining $T$. Fix $0<\alpha<1/2$. Let
  $\hat v_\beta$ be the $\beta$-quantile of the conditional law of $T^\star$ and $\hat x_\beta$ that
  of $\hat\theta^\star$. The one-sided percentile-$t$ interval
  $(-\infty,\hat\theta-n^{-1/2}\hat\sigma\hat v_\alpha]$ has coverage
  $1-\alpha+O(n^{-1})$, while the one-sided normal-theory interval
  $(-\infty,\hat\theta+n^{-1/2}\hat\sigma z_\alpha]$ and the one-sided
  percentile interval $(-\infty,\hat x_{1-\alpha}]$ have coverage
  $1-\alpha+O(n^{-1/2})$. The corresponding two-sided equal-tailed intervals
  of nominal coverage $1-2\alpha$ all have coverage $1-2\alpha+O(n^{-1})$,
  and the symmetric percentile-$t$ interval
  $[\hat\theta-n^{-1/2}\hat\sigma\hat w,\hat\theta+n^{-1/2}\hat\sigma\hat w]$,
  with $\hat w$ the $(1-2\alpha)$-quantile of the conditional law of
  $|T^\star|$, has coverage $1-2\alpha+O(n^{-2})$. Absent; it rests on 102.50 and its bootstrap analogue.

## 103. Nonparametric and high-dimensional inference

Mathlib supplies the decision-theoretic frame of this section (average,
Bayes, and minimax risk of randomized estimators, with the bound of Bayes by
minimax risk and data-processing inequalities), the total variation distance
with its Hahn-decomposition formula, the Kullback–Leibler divergence with its
chain rule and data processing, the Hamming distance and covering and packing
numbers, the one-dimensional central limit theorem and the Cramér–Wold
device, Brownian motion, reproducing-kernel Hilbert spaces with Moore's
theorem, the Hilbert projection onto closed convex sets, covariance operators
of measures on Hilbert spaces, and sub-Gaussian tail bounds. TauCeti adds the
probability integral transform and quantile sampling, the exact laws of order
statistics and of binomial and Poisson-binomial counts, Pinsker's inequality
and the tensorization of the divergence over two factors, chi-squared laws of
Gaussian sums of squares and of Gaussian projections onto subspaces,
approximate identities in $L^p$, the eigenbasis of a compact symmetric
operator, Ky Fan's trace inequality with its attainment for positive
operators, a dimension-free Davis–Kahan $\sin\Theta$ theorem with Weyl's
eigenvalue bound and the Yu–Wang–Samworth eigenvector bound, unitarily
invariant matrix norms, Gaussian conditioning, Bernstein's inequality and
sub-exponential tails, an operator-norm tail bound for sub-Gaussian
matrices, volumetric covering bounds, a lower bound for Gaussian maxima,
Gaussian concentration, and the Marchenko–Pastur law as a measure. Statlib
adds the identity between the minimal sum of the two error probabilities
of a test and total variation, the Bretagnolle–Huber inequality, the
$n$-fold tensorization of the divergence, the squared Hellinger distance,
mutual information, and a Fano-type bound for Bayes risks. No estimator of
the section is defined in any of the three libraries. The principal
omissions are therefore the whole statistical layer: the empirical-process
limits behind goodness-of-fit tests, rank statistics and their asymptotics,
kernel and spline smoothing, shape-constrained estimation, the minimax
theory of the Gaussian sequence and regression models with the reductions
to testing (Le Cam, Fano, Assouad) stated as lower bounds and the
Varshamov–Gilbert packing, the lasso and sparse recovery, penalized model
selection, false-discovery control, structured covariance estimation, and
the random-matrix asymptotics of sample covariance matrices. The representer
theorem, Le Cam's two-point bound, and Fano's bound are selected although
each follows from library results by a short argument, indicated in the
assessment.

Sources: [mathematical synopsis](SYNOPSIS103.md); [combined coverage inventory](STRUCTURE103.md).

Unless stated otherwise, $X_1,\ldots,X_n$ are independent copies of a real
random variable with distribution function $F$ and, when it exists, density
$f$; $F_n$ is the empirical distribution function. A **Brownian bridge**
$B^0$ is the centered continuous Gaussian process on $[0,1]$ with covariance
$s\wedge t-st$. Write $\Rightarrow$ for convergence in law and $z_\alpha$ for
the upper $\alpha$-quantile of the standard normal law $\Phi$. Infima over
"estimators" run over all measurable functions of the data.

Total variation follows the synopsis convention
$\|P-Q\|_{\mathrm{TV}}=\sup_A|P(A)-Q(A)|\in[0,1]$; Mathlib's distance between
probability measures is twice this. $D(P\|Q)$ is the Kullback–Leibler
divergence. In the **Gaussian sequence model** one observes
$Y_i=\theta_i+\varepsilon\xi_i$ (or $\sigma\xi_i$) with independent standard
normal $\xi_i$; the white-noise model $dY(t)=f(t)\,dt+\varepsilon\,dW(t)$ on
$[0,1]$ is equivalent to it through an orthonormal basis. For an
$n\times p$ design $X$ and $Y=X\beta+\varepsilon$, the **lasso** is any
minimizer of $(2n)^{-1}\|Y-X\beta\|_2^2+\lambda\|\beta\|_1$.

### Ranks, smoothing, shape constraints, minimax estimation, and functional data

A **kernel density estimator** with bandwidth $h>0$ and kernel $K$ is
$\hat f_h(x)=(nh)^{-1}\sum_iK((x-X_i)/h)$. Write $\mu_2(K)=\int u^2K(u)\,du$
and $R(K)=\int K^2$. For regression data $(X_i,Y_i)$, independent copies of
$(X,Y)$, put $m(x)=\mathbb E[Y\mid X=x]$; the **Nadaraya–Watson** estimator
weights $Y_i$ by $K_h(X_i-x)/\sum_jK_h(X_j-x)$.

* **103.1. Kolmogorov–Smirnov statistic.** If $F$ is continuous, the law of
  $\sup_x|F_n(x)-F(x)|$ does not depend on $F$, and as $n\to\infty$
  $$\sqrt n\sup_x|F_n(x)-F(x)|\Rightarrow\sup_{t\in[0,1]}|B^0(t)|,\qquad
  P\bigl(\sup_t|B^0(t)|\le x\bigr)
  =1-2\sum_{k=1}^\infty(-1)^{k-1}e^{-2k^2x^2}\quad(x>0).$$
  For every $n$ and every $x>0$ (Dvoretzky–Kiefer–Wolfowitz, with Massart's
  constant),
  $P\bigl(\sqrt n\sup_x|F_n(x)-F(x)|>x\bigr)\le2e^{-2x^2}$. TauCeti proves
  the probability integral transform for atomless laws and quantile
  sampling for every law on the line, from which the distribution-freeness
  follows by a short reduction to uniform samples that is not stated.
  Mathlib defines Brownian motion through its finite-dimensional laws;
  missing are the Brownian bridge, weak convergence in $\ell^\infty$,
  Donsker's theorem, the Kolmogorov distribution, and the inequality.

* **103.4. Kernel density asymptotics.** Let $K$ be a bounded symmetric
  probability density with finite $\mu_2(K)$ and $R(K)$, and let $f$ be twice
  continuously differentiable with $f$ and $f''$ square-integrable. If $f''$
  is bounded, $f(x)>0$, $h\to0$, $nh\to\infty$, and $nh^5=O(1)$, then
  $$\sqrt{nh}\Bigl(\hat f_h(x)-f(x)-\tfrac12h^2\mu_2(K)f''(x)\Bigr)
  \Rightarrow N\bigl(0,R(K)f(x)\bigr).$$
  If $h\to0$ and $nh\to\infty$,
  $$\mathbb E\int(\hat f_h-f)^2
  =\tfrac14h^4\mu_2(K)^2\int(f'')^2+\frac{R(K)}{nh}
  +o\Bigl(h^4+\frac1{nh}\Bigr),$$
  and if $\int(f'')^2>0$ the leading term is minimized by
  $h_n^*=\bigl(R(K)/(\mu_2(K)^2\int(f'')^2\,n)\bigr)^{1/5}$. Mathlib proves
  pointwise convergence of convolutions with shrinking smooth bump functions
  at points of continuity, the qualitative deterministic bias limit for such
  kernels. Missing are the estimator, the second-order bias expansion, the
  variance computation, the central limit theorem for the resulting
  triangular array (Mathlib's is for independent identically distributed
  sums), and the integrated-error expansion.

* **103.5. Universal $L^1$ consistency.** Let $K$ be a bounded integrable
  compactly supported kernel on $\mathbb R^d$ with $\int K=1$. If $h\to0$ and
  $nh^d\to\infty$, then $\int|\hat f_h-f|\to0$ almost surely for every
  density $f$ on $\mathbb R^d$. TauCeti's $L^p$ approximate-identity theorem
  with $p=1$ gives the bias half, $\|K_h*f-f\|_1\to0$, for normalized smooth
  bump kernels only. Missing are the stochastic half, which needs an $L^1$
  or Vapnik–Chervonenkis-type uniform law for the empirical measure, and
  general kernels.

* **103.7. Stone's theorem.** Assume $\mathbb EY^2<\infty$. For the
  Nadaraya–Watson estimator $\hat m_n$ on $\mathbb R^d$, with $0/0$ read as
  $0$ and a nonnegative bounded compactly supported kernel bounded below by
  a positive constant near zero, $h\to0$ and $nh^d\to\infty$ imply
  $$\mathbb E\bigl[(\hat m_n(X)-m(X))^2\bigm|X_1,Y_1,\ldots,X_n,Y_n\bigr]\to0$$
  in probability, for every distribution of $(X,Y)$. The same $L^2$
  consistency holds for $k$-nearest-neighbour regression when $k\to\infty$
  and $k/n\to0$, for every such distribution in which $X$ has a density.
  No library defines a regression estimator, and no part of this
  distribution-free consistency theory is present.

* **103.8. Representer theorem.** Let $\mathcal H$ be a reproducing-kernel
  Hilbert space of real functions on $\mathcal X$ with kernel $K$, and let the
  loss $L(y,u)$ depend on $f$ only through $u=f(X_i)$. A minimizer of
  $$\frac1n\sum_{i=1}^nL(Y_i,f(X_i))+\lambda\|f\|_{\mathcal H}^2,
  \qquad\lambda>0,$$
  over $f\in\mathcal H$ has the form $f=\sum_{i=1}^n\alpha_iK(X_i,\cdot)$. In
  particular, for $n\ge2$ distinct design points in $[a,b]$, the criterion
  $\sum_i(Y_i-f(x_i))^2+\lambda\int_a^b(f'')^2$ on the Sobolev space of
  functions with square-integrable second derivative has a minimizer that is
  a natural cubic spline with knots at the design points. The general
  statement follows from Mathlib's reproducing property and the Hilbert
  projection theorem: writing $f=f_\parallel+f_\perp$ with $f_\parallel$ in
  the span of $K(X_1,\cdot),\ldots,K(X_n,\cdot)$, the reproducing property
  gives $f_\perp(X_i)=0$, so the loss is unchanged while the penalty strictly
  decreases unless $f_\perp=0$. No penalized criterion is formalized, and the
  spline case needs Sobolev functions on an interval and the
  characterization of natural cubic splines, which are absent.

* **103.9. Pinsker's theorem and the Sobolev rate.** In the Gaussian sequence
  model let $\Theta$ be the ellipsoid $\sum_ja_j^2\theta_j^2\le R$, with $a_j$
  positive, nondecreasing, and $a_j\to\infty$. Let $R_N(\varepsilon)$ be the
  minimax mean squared error over $\Theta$ among all estimators and
  $R_L(\varepsilon)$ that among linear estimators $\hat\theta_j=c_jY_j$.
  Then $R_N(\varepsilon)/R_L(\varepsilon)\to1$ as $\varepsilon\to0$, and
  $R_L$ is attained by the weights $c_j=(1-a_j/\mu)_+$ for a suitable
  $\mu=\mu(\varepsilon)>0$. If $a_j=j^\beta$ with $\beta>0$,
  $$R_N(\varepsilon)\sim P_\beta R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)},
  \qquad
  P_\beta=(2\beta+1)^{1/(2\beta+1)}
  \Bigl(\frac\beta{\beta+1}\Bigr)^{2\beta/(2\beta+1)}.$$
  If only $cj^\beta\le a_j\le Cj^\beta$, then $R_N(\varepsilon)$ is bounded
  above and below by positive multiples, depending only on $\beta,c,C$, of
  $R^{1/(2\beta+1)}\varepsilon^{4\beta/(2\beta+1)}$ for all small
  $\varepsilon$. Mathlib defines the minimax risk; the sequence model,
  ellipsoids, and every part of the theorem are missing.

* **103.11. Grenander estimator.** Let $f$ be a density vanishing on
  $(-\infty,0)$ and decreasing on $[0,\infty)$, continuous at $x_0>0$
  with $f'(x_0)<0$. The maximum
  likelihood estimator $\hat f_n$ among decreasing densities is the left
  slope of the least concave majorant of $F_n$, and
  $$n^{1/3}\bigl(\hat f_n(x_0)-f(x_0)\bigr)
  \Rightarrow\bigl|4f(x_0)f'(x_0)\bigr|^{1/3}Z,\qquad
  Z=\mathop{\mathrm{argmax}}_{t\in\mathbb R}\bigl(W(t)-t^2\bigr),$$
  with $W$ standard two-sided Brownian motion (Chernoff's distribution, up
  to scale). Mathlib's Brownian motion on $[0,\infty)$ is the only
  supporting material; the estimator, the least concave majorant,
  two-sided Brownian motion with Chernoff's distribution, and the
  cube-root limit are missing.

### Rank scores, rank correlation, and goodness of fit

Let $U_{N(1)}<\cdots<U_{N(N)}$ be uniform order statistics. A
**score-generating function** is a measurable, not almost everywhere constant
$\varphi$ on $(0,1)$ with $\int_0^1\varphi^2<\infty$; its **exact scores** are
$a_N(i)=\mathbb E\varphi(U_{N(i)})$ and its **approximate scores**
$\varphi(i/(N+1))$. Bars denote averages.

* **103.14. Score-generating functions and locally most powerful rank
  tests.** Let $X_1,\ldots,X_N$ be independent with a common continuous
  distribution function $F$, let $R_i$ be their ranks, and let
  $T_N=\sum_ic_{N,i}a_N(R_i)$ with exact scores. Then
  $\mathbb ET_N=N\bar c_N\bar a_N$,
  $$\mathop{\mathrm{Var}}T_N=\frac1{N-1}\sum_i(c_{N,i}-\bar c_N)^2
  \sum_i\bigl(a_N(i)-\bar a_N\bigr)^2,$$
  and $T_N$ is asymptotically equivalent, with difference of negligible
  variance relative to $\mathop{\mathrm{Var}}T_N$, to
  $N\bar c_N\bar a_N+\sum_i(c_{N,i}-\bar c_N)\varphi(F(X_i))$. Hence the
  standardized statistic is asymptotically normal when
  $\max_i(c_{N,i}-\bar c_N)^2/\sum_i(c_{N,i}-\bar c_N)^2\to0$; the same
  holds for approximate scores if $\varphi$ is continuous almost everywhere
  and $N^{-1}\sum_i\varphi^2(i/(N+1))\to\int_0^1\varphi^2$. If $X_i$ has
  density $f(x-\theta c_{N,i})$ with $f$ absolutely continuous of finite
  Fisher information for location, the locally most powerful rank test of
  $\theta=0$ against $\theta>0$ rejects for large $T_N$ with exact scores
  generated by $\varphi_f(u)=-(f'/f)(F^{-1}(u))$. TauCeti proves the beta
  laws of uniform order statistics and the representation of order
  statistics through quantiles, so the exact scores are integrals against
  known laws. Missing are ranks and the uniformity of the rank vector, the
  moment formulas, the Hájek projection, a central limit theorem for
  triangular arrays, and Fisher information for location.

* **103.17. Cramér–von Mises and two-sample Kolmogorov–Smirnov limits.** If
  $F$ is continuous, $W_n^2=n\int(F_n-F)^2\,dF$ is distribution-free and
  $$W_n^2\Rightarrow\int_0^1B^0(t)^2\,dt
  \stackrel{d}{=}\sum_{j=1}^\infty\frac{Z_j^2}{j^2\pi^2}$$
  with $Z_j$ independent standard normal. For independent samples of sizes
  $m,n$ with empirical distribution functions $F_m,G_n$ from a common
  continuous law, $D_{m,n}=\sup_x|F_m(x)-G_n(x)|$ is distribution-free and
  $\sqrt{mn/(m+n)}\,D_{m,n}\Rightarrow\sup_t|B^0(t)|$ as
  $\min(m,n)\to\infty$; under differing laws the normalized statistic tends
  to infinity in probability. For a parametric family with
  $\sup_x|F_{\theta+u}(x)-F_\theta(x)-u^\top\dot F_\theta(x)|=o(|u|)$ and an
  asymptotically linear estimator
  $\sqrt n(\hat\theta_n-\theta)=n^{-1/2}\sum_i\psi_\theta(X_i)+o_P(1)$ with
  $\mathbb E\psi_\theta(X)=0$ and $\mathbb E|\psi_\theta(X)|^2<\infty$,
  $\sqrt n(F_n-F_{\hat\theta_n})$ converges in law in $\ell^\infty(\mathbb R)$
  to a centered Gaussian process $G$ with covariance
  $$F_\theta(x\wedge y)-F_\theta(x)F_\theta(y)
  -\dot F_\theta(x)^\top\mathbb E[\psi_\theta1_{\{X\le y\}}]
  -\dot F_\theta(y)^\top\mathbb E[\psi_\theta1_{\{X\le x\}}]
  +\dot F_\theta(x)^\top\mathbb E[\psi_\theta\psi_\theta^\top]\dot F_\theta(y),$$
  and $\sqrt n\sup_x|F_n-F_{\hat\theta_n}|\Rightarrow\sup_x|G(x)|$. The
  libraries supply only the ingredients listed under 103.1; the
  Karhunen–Loève expansion of the bridge and all three limit theorems are
  missing.

### Exact ranks, smoothing bias, and shape constraints

For $\beta>0$ and $L>0$ let $\ell$ be the largest integer strictly smaller
than $\beta$. The **Hölder class** $\Sigma(\beta,L)$ consists of the
functions on $[0,1]$ that are $\ell$ times differentiable with
$|f^{(\ell)}(x)-f^{(\ell)}(x')|\le L|x-x'|^{\beta-\ell}$.

* **103.22. Hölder regression rates.** Let $Y_i=f(i/n)+\xi_i$,
  $i=1,\ldots,n$, with $\xi_i$ independent $N(0,\sigma^2)$, $\sigma>0$. Write
  $R_n^{(2)}=\inf_{\hat f}\sup_{f\in\Sigma(\beta,L)}\mathbb E\|\hat f-f\|_2^2$
  and $R_n^{(\infty)}$ for the same with $\|\cdot\|_\infty^2$. Then
  $$0<\liminf_nn^{2\beta/(2\beta+1)}R_n^{(2)}
  \le\limsup_nn^{2\beta/(2\beta+1)}R_n^{(2)}<\infty,$$
  and the same holds for $R_n^{(\infty)}$ with $n^{2\beta/(2\beta+1)}$
  replaced by $(n/\log n)^{2\beta/(2\beta+1)}$. In the $L^2$ case the upper
  bound is attained by the local polynomial estimator of degree $\ell$ with
  bandwidth $h=c\,n^{-1/(2\beta+1)}$, $c>0$, and a kernel $K$ with
  $K_{\min}1_{\{|u|\le\Delta\}}\le K(u)\le K_{\max}1_{\{|u|\le1\}}$ for
  constants $K_{\min},\Delta>0$ and $K_{\max}<\infty$. Mathlib defines Hölder
  conditions and the minimax risk; the estimators, the upper bounds, and the
  lower bounds (which need 103.39 and 103.40, for which Statlib's testing
  identity and divergence bounds are ingredients) are missing.

### Bandwidth selection, linear smoothers, and density rates

A **kernel of order** $\ell\ge1$ satisfies $\int K=1$ and $\int u^jK(u)\,du=0$
for $1\le j\le\ell$. The **Hölder density class** $\mathcal P(\beta,L)$ is the
set of probability densities on $\mathbb R$ with the Hölder condition of
$\Sigma(\beta,L)$.

* **103.26. Minimax rates of density estimation.** Let $K$ be a kernel of
  order $\ell$ with $\int K^2<\infty$ and $\int|u|^\beta|K(u)|\,du<\infty$,
  and let $h=cn^{-1/(2\beta+1)}$. Then
  $$\sup_{x_0\in\mathbb R}\sup_{f\in\mathcal P(\beta,L)}
  \mathbb E\bigl(\hat f_h(x_0)-f(x_0)\bigr)^2\le Cn^{-2\beta/(2\beta+1)}$$
  for all $n$, with $C$ depending only on $\beta,L,K,c$. Conversely there is
  $c'>0$, depending only on $\beta,L$, with
  $\liminf_nn^{2\beta/(2\beta+1)}\inf_{T_n}\sup_{f\in\mathcal P(\beta,L)}
  \mathbb E(T_n(x_0)-f(x_0))^2\ge c'$ for every $x_0$, and the same lower
  bound holds for $\mathbb E\int(T_n-f)^2$. For an integer $m\ge1$ and the
  class $\mathcal F_{m,M}$ of densities with $m$ continuous derivatives and
  $\int(f^{(m)})^2\le M$, kernels of order $m-1$ with
  $\int|y|^m|K(y)|\,dy<\infty$ and bandwidth $n^{-1/(2m+1)}$ give
  $\sup_{f\in\mathcal F_{m,M}}\mathbb E\int(\hat f_h-f)^2\le
  C_{m,M}n^{-2m/(2m+1)}$, with $C_{m,M}$ depending only on $m,M,K$, and
  Assouad's lemma gives a lower bound $D_{m,M}n^{-2m/(2m+1)}$, with
  $D_{m,M}>0$ depending only on $m,M$, for every estimator and all
  sufficiently large $n$. No part is
  present; higher-order kernels and the lower-bound reductions are absent.

### Risk bounds under shape constraints

The squared Hellinger distance is $H^2(f,g)=\int(\sqrt f-\sqrt g)^2$, and
$\mathcal F_d$ is the class of upper semicontinuous log-concave densities on
$\mathbb R^d$.

* **103.27. Risk of isotonic regression.** Let
  $Y_i=\theta_i^*+\varepsilon_i$, $i=1,\ldots,n$, with
  $\theta_1^*\le\cdots\le\theta_n^*$ and independent errors of mean zero and
  variance one, and let $\hat\theta$ be the least-squares projection onto
  nondecreasing sequences. For a universal $C$,
  $$\frac1n\mathbb E\|\hat\theta-\theta^*\|^2
  \le C\left\{\Bigl(\frac{\theta_n^*-\theta_1^*}n\Bigr)^{2/3}
  +\frac{\log(en)}n\right\}.$$
  The worst-case risk over nondecreasing sequences with
  $\|\theta^*\|_\infty\le1$ is therefore at most $C'n^{-2/3}$, and for
  standard normal errors no estimator does better than $cn^{-2/3}$ over
  this class. Mathlib's Hilbert projection theorem gives existence and
  uniqueness of $\hat\theta$; the risk bound and the lower bound are
  missing.

* **103.28. Log-concave maximum likelihood.** Let $P$ be a probability
  measure on $\mathbb R^d$ with finite first moment that gives probability
  less than one to every hyperplane. Then $\int\log f\,dP$ has a unique
  maximizer over $\mathcal F_d$, the log-concave projection of $P$, whose
  positivity set lies between the interior of the convex support of $P$ and
  that support. For $n\ge d+1$ points with $d$-dimensional convex hull $C_n$,
  this gives a unique maximum likelihood estimator $\hat f_n$, supported on
  $C_n$, whose logarithm is a tent function. For samples from
  $f_0\in\mathcal F_d$ and $n\ge d+1$, with $C_d$ depending only on $d$,
  $$\sup_{f_0\in\mathcal F_d}\mathbb EH^2(\hat f_n,f_0)\le C_d\cdot
  \begin{cases}n^{-4/5},&d=1,\\ n^{-2/(d+1)}\log n,&d\ge2,\end{cases}$$
  and, for some $c_d>0$ depending only on $d$, every estimator has
  worst-case risk at least $c_dn^{-4/5}$ for $d=1$
  and $c_dn^{-2/(d+1)}$ for $d\ge2$. TauCeti proves the Prékopa–Leindler and
  Brunn–Minkowski inequalities and the log-concavity of marginals of
  log-concave functions, which do not bear on the estimator. Statlib
  defines the squared Hellinger distance, normalized as $\frac12H^2$, with
  its comparison with total variation. Log-concave densities as a
  statistical class, the log-concave projection, and the whole statement
  are missing.

### Functional data analysis

Let $X$ be a random element of a separable Hilbert space $H$ with
$\mathbb E\|X\|^2<\infty$, mean $\mu$, and covariance operator
$C=\mathbb E[(X-\mu)\otimes(X-\mu)]$, with eigenvalues $\lambda_j$ and
orthonormal eigenfunctions $\varphi_j$; $\hat C_n$ is the empirical
covariance operator, with eigenpairs $(\hat\lambda_j,\hat\varphi_j)$.

* **103.29. Karhunen–Loève expansion and the Hilbertian central limit
  theorem.** The operator $C$ is compact, self-adjoint, nonnegative, and
  trace-class. For positive eigenvalues the variables
  $\xi_j=\langle X-\mu,\varphi_j\rangle/\sqrt{\lambda_j}$ are uncorrelated
  with mean $0$ and variance $1$, and
  $X=\mu+\sum_j\sqrt{\lambda_j}\,\xi_j\varphi_j$, with convergence in $L^2$
  and almost surely in $H$. For independent copies,
  $\sqrt n(\bar X_n-\mu)$ converges in law in $H$ to the centered Gaussian
  element with covariance operator $C$. Mathlib defines the covariance
  operator and proves it positive; TauCeti proves that a compact symmetric
  operator has a Hilbert basis of eigenvectors. Missing are compactness and
  the trace-class property of $C$, the random series, and any central limit
  theorem in infinite dimension.

* **103.30. Principal components of the empirical covariance.** If
  $\lambda_j$ is simple and positive and $\mathbb E\|X\|^4<\infty$, then
  $$\sqrt n(\hat\lambda_j-\lambda_j)
  \Rightarrow N\bigl(0,\mathop{\mathrm{Var}}(\langle X-\mu,\varphi_j\rangle^2)\bigr),$$
  with variance $2\lambda_j^2$ for Gaussian $X$. With decreasing order and
  the sign chosen so that $\langle\hat\varphi_j,\varphi_j\rangle\ge0$,
  $\|\hat\varphi_j-\varphi_j\|=O_P(n^{-1/2})$, and
  $$\hat\varphi_j-\varphi_j
  =\sum_{k\ne j}\frac{\langle(\hat C_n-C)\varphi_j,\varphi_k\rangle}
  {\lambda_j-\lambda_k}\varphi_k+o_P(n^{-1/2}),$$
  with the zero eigenspace included in the sum when present. TauCeti's
  dimension-free Davis–Kahan theorem, and in finite dimension its
  Yu–Wang–Samworth eigenvector bound, are the natural deterministic input
  for the $O_P(n^{-1/2})$ bound; the perturbation expansions and the limit
  laws are missing.

* **103.31. Optimality of functional principal components.** With
  eigenvalues in decreasing order,
  $$\inf_{\dim V=k}\mathbb E\|X-\mu-P_V(X-\mu)\|^2=\sum_{j>k}\lambda_j,$$
  the infimum over orthogonal projections onto $k$-dimensional subspaces;
  the first $k$ eigenfunctions span a minimizer, unique if
  $\lambda_k>\lambda_{k+1}$. The entry is partly covered: TauCeti's Ky Fan
  trace inequality gives the deterministic inequality in finite dimension,
  through
  $\mathbb E\|X-\mu-P_V(X-\mu)\|^2=\mathop{\mathrm{tr}}C-\mathop{\mathrm{tr}}(P_VC)$,
  and for a positive operator the bound is attained by some orthonormal
  family of $k$ vectors. Missing are the expectation formulation,
  attainment by the leading eigenvectors, uniqueness, and the trace-class
  Hilbert-space case.

### High-dimensional and large-scale inference

In the **Gaussian regression model** one observes $Y=f+\sigma\xi$ in
$\mathbb R^n$; for linear subspaces $S_m$ of dimension $d_m$, $\hat f_m$ is
the orthogonal projection of $Y$ onto $S_m$, and $\|v\|_n^2=n^{-1}\|v\|_2^2$.
For an index set $S$ the **compatibility constant** is
$$\kappa^2(S,L)=\inf\Bigl\{\frac{|S|\,\|X\delta\|_2^2}{n\|\delta_S\|_1^2}:
\delta\ne0,\ \|\delta_{S^c}\|_1\le L\|\delta_S\|_1\Bigr\}.$$
For $m$ hypotheses with ordered valid $p$-values
$p_{(1)}\le\cdots\le p_{(m)}$, of which $m_0$ are true nulls, $V$ and $R$
count false and all rejections.

* **103.33. Sparse minimax rate.** In the Gaussian sequence model
  $Y=\theta+\sigma\xi$ in $\mathbb R^p$ there are universal $0<c\le C$ such
  that, for $1\le s\le p/2$, the minimax mean squared error over vectors
  with at most $s$ nonzero coordinates lies between $c\sigma^2s\log(p/s)$
  and $C\sigma^2s\log(p/s)$; soft thresholding at $\sigma\sqrt{2\log(p/s)}$
  attains the upper bound, and the universal threshold
  $\sigma\sqrt{2\log p}$ has risk at most $(2\log p+1)(s+1)\sigma^2$. No
  part is present beyond Mathlib's definition of minimax risk; for the
  lower bound, Statlib's Fano-type bound for Bayes risks is an ingredient,
  and the sparse packing it needs is absent.

* **103.34. Lasso under compatibility.** Let $S$ be nonempty and
  $\lambda>0$. Suppose $\beta$ is supported on $S$
  and $\lambda\ge2n^{-1}\|X^\top\varepsilon\|_\infty$. If $\kappa(S,3)>0$,
  every lasso solution satisfies
  $$\frac1n\|X(\hat\beta-\beta)\|_2^2\le\frac{9\lambda^2|S|}{4\kappa^2(S,3)},
  \qquad\|\hat\beta-\beta\|_1\le\frac{6\lambda|S|}{\kappa^2(S,3)},$$
  and the error lies in the cone $\|\delta_{S^c}\|_1\le3\|\delta_S\|_1$. If
  $n^{-1}\|X\delta\|_2^2\ge\kappa\|\delta\|_2^2$ on that cone, then
  $\|\hat\beta-\beta\|_2\le3\sqrt{|S|}\lambda/\kappa$. For independent
  centered unit-variance sub-Gaussian design entries, there are constants
  $C,c,\kappa_0>0$ depending only on the sub-Gaussian parameter such that
  the restricted eigenvalue condition holds with $\kappa=\kappa_0$ with
  probability at least $1-2e^{-cn}$ when $n\ge C|S|\log(ep/|S|)$; for columns with $\|X_{\cdot j}\|_2^2/n\le1$ and
  independent $N(0,\sigma^2)$ errors, $\lambda=2\sigma\sqrt{2(\log p+t)/n}$
  meets the noise condition with probability at least $1-2e^{-t}$. The
  deterministic part is finite-dimensional convex analysis, and the noise
  event follows from Mathlib's Gaussian tail bound by a union bound. For
  random designs, TauCeti bounds the operator norm of a sub-Gaussian matrix
  from above with exponential probability, by a net argument, and bounds
  covering numbers by volume; the lower restricted eigenvalue bound, uniform
  over the cone, is not stated. The lasso, the cone argument, and the
  restricted eigenvalue property of random designs are missing.

* **103.35. Penalized model selection.** Let $(\pi_m)$ be positive weights
  with $\sum_m\pi_m\le1$ for a countable collection $(S_m)$. There is a
  universal $\kappa_0$ such that for every $\kappa>\kappa_0$ and
  $\mathop{\mathrm{pen}}(m)\ge\kappa\sigma^2n^{-1}(d_m+\log(1/\pi_m))$, the
  selector $\hat m$ minimizing $\|Y-\hat f_m\|_n^2+\mathop{\mathrm{pen}}(m)$
  satisfies
  $$\mathbb E\|\hat f_{\hat m}-f\|_n^2\le C(\kappa)\Bigl(\inf_m\Bigl(
  \inf_{g\in S_m}\|g-f\|_n^2+\mathop{\mathrm{pen}}(m)\Bigr)+\frac{\sigma^2}n\Bigr),$$
  where $C(\kappa)$ depends only on $\kappa$.
  TauCeti proves that $\|P_S\xi\|^2$ has the $\chi^2_{\dim S}$ law for a
  standard Gaussian $\xi$ and a linear subspace $S$, and a Gaussian
  concentration inequality for continuously differentiable functions; the
  norm of a projection is Lipschitz but not differentiable at the origin,
  so that inequality does not apply to it directly. The oracle inequality,
  which needs Gaussian concentration for the projected noise uniformly over
  the collection, is missing.

* **103.37. Benjamini–Hochberg procedure.** Fix $\alpha\in(0,1)$, let
  $k=\max\{i:p_{(i)}\le i\alpha/m\}$ ($k=0$ if no such $i$), and reject the
  hypotheses of $p_{(1)},\ldots,p_{(k)}$. If the null $p$-values are
  independent of each other and of the non-null ones, or if the $p$-value
  vector $p$ is positively regression dependent on the subset of null
  coordinates (for every set $D\subset[0,1]^m$ such that $x\in D$ and
  $x\le y$ coordinatewise imply $y\in D$, and every true null $i$,
  $t\mapsto P(p\in D\mid p_i=t)$ is nondecreasing), then
  $$\mathbb E\Bigl[\frac V{\max(R,1)}\Bigr]\le\alpha\frac{m_0}m\le\alpha.$$
  No library defines $p$-values or multiple-testing procedures; the
  argument is finite and combinatorial–probabilistic, but no part is
  present.

* **103.38. Tracy–Widom law and spiked covariance.** Let $X$ be $n\times p$
  with independent standard normal entries and $\ell_{\max}$ the largest
  eigenvalue of $n^{-1}X^\top X$. As $n,p\to\infty$ with $p/n\to y\in(0,\infty)$,
  $$\frac{\ell_{\max}-\mu_{n,p}}{\sigma_{n,p}}\Rightarrow F_1,\qquad
  \mu_{n,p}=\frac{(\sqrt{n-1}+\sqrt p)^2}n,\quad
  \sigma_{n,p}=\frac{(\sqrt{n-1}+\sqrt p)
  ((n-1)^{-1/2}+p^{-1/2})^{1/3}}n,$$
  where $F_1$ is the Tracy–Widom law of the Gaussian orthogonal ensemble. In
  the spiked model with rows $N(0,\Sigma)$ and one eigenvalue $\alpha$ of
  $\Sigma$, the rest $1$, $\ell_{\max}\to(1+\sqrt y)^2$ almost surely when
  $1<\alpha\le1+\sqrt y$ and $\ell_{\max}\to\alpha+y\alpha/(\alpha-1)$ when
  $\alpha>1+\sqrt y$. TauCeti has the Wishart laws, sample second-moment
  matrices with polynomial entrywise deviation bounds, the Marchenko–Pastur
  law as a measure with its density and atom, the Gaussian orthogonal and
  unitary ensembles, and the method of moments for weak convergence. No
  spectral limit theorem is stated: the Marchenko–Pastur limit, the edge
  asymptotics, the Tracy–Widom law, and the spike transition are missing.

### Lower bounds, regularization, and multiplicity

* **103.39. Le Cam's two-point method.** If two parameters are at distance
  at least $2s$, every estimator satisfies
  $$\max_{j=0,1}P_j\bigl(d(\hat\theta,\theta_j)\ge s\bigr)
  \ge\tfrac12\bigl(1-\|P_0-P_1\|_{\mathrm{TV}}\bigr),$$
  so for a nonnegative increasing loss $\ell$ the minimax risk is at least
  $\ell(s)(1-\|P_0-P_1\|_{\mathrm{TV}})/2$. For product laws
  $P_j=Q_j^{\otimes n}$, $D(P_0\|P_1)=nD(Q_0\|Q_1)$ and
  $\|P_0-P_1\|_{\mathrm{TV}}\le\sqrt{D(P_0\|P_1)/2}$. The argument is short:
  the test choosing the nearer parameter has errors bounded by the two
  probabilities, and the sum of errors of any test is at least
  $1-\|P_0-P_1\|_{\mathrm{TV}}$. Statlib proves this testing identity, as the
  value of the Bayes risk of testing $P_0$ against $P_1$ under the prior
  with unit masses, and the identity $D(Q_0^{\otimes n}\|Q_1^{\otimes n})
  =nD(Q_0\|Q_1)$; TauCeti proves Pinsker's inequality, stated for Mathlib's
  total variation distance, which is twice the synopsis convention. Missing
  is the reduction from an estimator to a test, so the two-point lower bound
  itself is not stated.

* **103.40. Fano's method.** Let $\theta_1,\ldots,\theta_M$, $M\ge2$, be
  $2s$-separated with observation laws $P_j$, let $J$ be uniform on
  $\{1,\ldots,M\}$ and $X\mid J=j\sim P_j$. Every estimator satisfies
  $$\sup_jP_j\bigl(d(\hat\theta,\theta_j)\ge s\bigr)
  \ge1-\frac{I(J;X)+\log2}{\log M},\qquad
  I(J;X)=\frac1M\sum_jD(P_j\|\bar P)\le\frac1M\sum_jD(P_j\|Q)$$
  for $\bar P=M^{-1}\sum_jP_j$ and any reference law $Q$ with finite right
  side. Statlib defines mutual information as the divergence of the joint
  law from the product of its marginals and proves the identities from
  which the two displayed formulas for $I(J;X)$ follow, and, for a loss
  with values in $[0,1]$, the bound $\mathrm{kl}(R_\pi^P,R_\pi^0)\le
  I(\pi\otimes P)$ of the binary divergence between the Bayes risk with
  observations and the Bayes risk without them. The $M$-ary bound is a
  short argument from this: under the $0$–$1$ loss and the uniform prior
  on $M$ indices every decision without data has risk $1-1/M$, and a lower
  bound for the binary divergence turns the inequality into the display.
  Missing are this specialization and the reduction from an estimator to
  an index test; the $M$-ary Fano bound is not stated.

### Packings and hypercube lower bounds

Write $\rho$ for the Hamming distance on $\Omega=\{0,1\}^m$.

* **103.45. Varshamov–Gilbert bound.** If $m\ge8$, there are points
  $\omega^{(0)}=0,\omega^{(1)},\ldots,\omega^{(M)}$ of $\{0,1\}^m$ with
  $\rho(\omega^{(j)},\omega^{(k)})\ge m/8$ for $j<k$ and $M\ge2^{m/8}$.
  Mathlib defines the Hamming distance and packing numbers, and TauCeti
  develops minimum distances of codes without an existence bound; its
  volumetric covering bounds concern balls of normed spaces, not Hamming
  balls. The
  statement follows by a counting argument: the Hamming balls of radius
  $m/8$ about a maximal separated set cover the cube, and Hoeffding's
  inequality, which Mathlib proves, bounds the size of each ball. It is not
  stated.

* **103.46. Assouad's lemma.** Let $(P_\omega)_{\omega\in\Omega}$ be laws
  indexed by $\Omega=\{0,1\}^m$. For every estimator $\hat\omega$ with
  values in $\Omega$,
  $$\max_\omega E_\omega\rho(\hat\omega,\omega)\ge\frac m2
  \min_{\rho(\omega,\omega')=1}\inf_\psi
  \bigl(P_\omega(\psi=1)+P_{\omega'}(\psi=0)\bigr).$$
  If neighbouring laws satisfy $\|P_\omega-P_{\omega'}\|_{\mathrm{TV}}\le\alpha<1$,
  the right side is at least $m(1-\alpha)/2$; if instead
  $D(P_\omega\|P_{\omega'})\le\alpha<\infty$, it is at least
  $\frac m2\max(\frac12e^{-\alpha},1-\sqrt{\alpha/2})$. If
  $d(\theta_\omega,\theta_{\omega'})^2\ge c\rho(\omega,\omega')$, every
  estimator $\hat\theta$ obeys
  $\max_\omega E_\omega d(\hat\theta,\theta_\omega)^2\ge
  (c/4)\max_\omega E_\omega\rho(\hat\omega,\omega)$ for a nearest index
  $\hat\omega$. The lemma combines $m$ two-point bounds of the kind in
  103.39. For each neighbouring pair, Statlib's testing identity gives the
  total-variation form of the bound and its Bretagnolle–Huber inequality
  the term $\frac12e^{-\alpha}$, and TauCeti's Pinsker inequality the term
  $1-\sqrt{\alpha/2}$; the reduction from the hypercube to its edges is not
  stated. Mathlib's Assouad bound on dual VC dimension is unrelated.

### Exact and stable sparse recovery

For $S\subset\{1,\ldots,p\}$, $X$ has the **restricted nullspace property**
with respect to $S$ if its kernel meets
$\{\delta:\|\delta_{S^c}\|_1\le\|\delta_S\|_1\}$ only at $0$. **Basis
pursuit** minimizes $\|b\|_1$ subject to $Xb=y$. The **restricted isometry
constant** $\delta_k(A)$ is the least $\delta\ge0$ with
$(1-\delta)\|v\|_2^2\le\|Av\|_2^2\le(1+\delta)\|v\|_2^2$ for all $k$-sparse
$v$, and $\sigma_s(\beta)_1$ is the $\ell^1$ error of best $s$-term
approximation.

* **103.48. Restricted nullspace and exact recovery.** For every $\beta$
  supported in $S$, basis pursuit with $y=X\beta$ has the unique solution
  $\beta$ if and only if $X$ has the restricted nullspace property with
  respect to $S$. If $\delta_{2s}(n^{-1/2}X)<1/3$, the property holds for
  every $S$ with $|S|\le s$. For independent centered unit-variance
  sub-Gaussian entries there are $C,c>0$, depending only on the
  sub-Gaussian parameter, such that $\delta_{2s}(n^{-1/2}X)<1/3$ with probability at
  least $1-2e^{-cn}$ whenever $n\ge Cs\log(ep/s)$. The equivalence and the
  restricted-isometry criterion are finite-dimensional linear algebra not
  present in any of the three libraries. For the probabilistic part TauCeti
  supplies an operator-norm tail bound for sub-Gaussian matrices, proved by
  a net argument, and volumetric covering bounds; the two-sided isometry
  bound uniformly over sparse supports is absent.

* **103.49. Stable recovery under restricted isometry.** If
  $\delta_{2s}(A)<4/\sqrt{41}$, then for every $\beta$ and $y$ with
  $\|A\beta-y\|_2\le\eta$, every minimizer $\beta^\sharp$ of $\|b\|_1$
  subject to $\|Ab-y\|_2\le\eta$ satisfies
  $$\|\beta^\sharp-\beta\|_1\le C\sigma_s(\beta)_1+D\sqrt s\,\eta,\qquad
  \|\beta^\sharp-\beta\|_2\le\frac C{\sqrt s}\sigma_s(\beta)_1+D\eta,$$
  with $C,D$ depending only on $\delta_{2s}(A)$. No part is present.

### Low-rank and structured covariance estimation

Let $x_1,\ldots,x_n$ be independent centered vectors in $\mathbb R^p$ with
covariance $\Sigma$, $\hat\Sigma=n^{-1}\sum_ix_ix_i^\top$, and let
$T_\lambda$ replace each matrix entry $u$ by $u1_{\{|u|>\lambda\}}$. For a
Gaussian vector the **precision matrix** is $\Theta=\Sigma^{-1}$, and the
**neighbourhood** $N(j)$ is the set of $k$ with $\Theta_{jk}\ne0$.
**Neighbourhood selection** runs a lasso of each coordinate on the others.

* **103.52. Thresholded covariance estimation.** Let $A$ be the $0$–$1$
  pattern of the nonzero entries of $\Sigma$ and $s$ the largest number of
  nonzero entries in a row. If $\|\hat\Sigma-\Sigma\|_{\max}\le\lambda$, then
  $\|T_\lambda(\hat\Sigma)-\Sigma\|_{\mathrm{op}}\le2\lambda\|A\|_{\mathrm{op}}
  \le2s\lambda$. If each coordinate is $\sigma$-sub-Gaussian and $n>\log p$,
  $\lambda=\sigma^2(8\sqrt{(\log p)/n}+\delta)$ makes this event hold with
  probability at least $1-8e^{-n\min(\delta,\delta^2)/16}$. TauCeti bounds
  the operator norm of a matrix with small entries by a dimension-dependent
  factor, has Chebyshev-type entrywise deviation bounds for sample
  second-moment matrices, and proves Bernstein's inequality and a
  Bernstein-type tail for sums of independent sub-exponential variables.
  Missing are the sparsity-adapted operator-norm bound, the sub-exponential
  property of products of sub-Gaussian coordinates, and hence the
  exponential entrywise concentration of $\hat\Sigma$.

* **103.53. Gaussian graphical model selection.** Let the data be $n$
  independent $N(0,\Sigma)$ vectors in $\mathbb R^p$ with $\Sigma_{jj}\le1$,
  at most $m$ neighbours per vertex, and $n\ge c_1m\log p$. Suppose that for
  each $j$ the covariance $\Gamma$ of the other coordinates satisfies
  $\max_{k\notin N(j)}\|\Gamma_{kN(j)}\Gamma_{N(j)N(j)}^{-1}\|_1\le1-\alpha$
  with $\alpha\in(0,1]$, and that
  $\|\Sigma_{N(j)N(j)}^{-1}\|_{\infty\to\infty}\le b$, $b\ge1$. With
  $\lambda=c_0\alpha^{-1}(\sqrt{(\log p)/n}+\delta)$, $0<\delta\le1$,
  neighbourhood selection by the "and" or the "or" rule includes no false
  edge and every edge with
  $|\Theta_{jk}|\ge7b\lambda\max(\Theta_{jj},\Theta_{kk})$, with probability
  at least $1-c_2\exp(-c_3n\min(\delta^2,1/m))$, for universal constants. For
  the graphical lasso with $\sigma$-sub-Gaussian coordinates, at most $m$
  nonzero entries per row of $\Theta$,
  $\lambda=8\sigma^2(\sqrt{(\log p)/n}+\delta)$, and
  $6(\|\Theta\|_{\mathrm{op}}+1)^2\lambda\sqrt{mp}<1$, with probability at
  least $1-8e^{-n\delta^2/16}$,
  $\|\hat\Theta-\Theta\|_F^2\le9(\|\Theta\|_{\mathrm{op}}+1)^4mp\lambda^2$.
  TauCeti's Gaussian conditioning formula is supporting, but the
  identification of the regression coefficients with $-\Theta_{jk}/\Theta_{jj}$
  is not stated; both estimators and their guarantees are missing.

### Principal components in high dimensions

* **103.54. Perturbation of the leading eigenvector.** Let $\Sigma$ be
  symmetric positive semidefinite with eigenvalues $\gamma_1>\gamma_2\ge\cdots$,
  gap $\nu=\gamma_1-\gamma_2$, and unit leading eigenvector $\theta^*$, and
  let $P$ be symmetric with $\|P\|_{\mathrm{op}}<\nu/2$. Then $\Sigma+P$ has
  a leading unit eigenvector $\hat\theta$, unique up to sign, and with
  $\langle\hat\theta,\theta^*\rangle\ge0$,
  $$\|\hat\theta-\theta^*\|_2\le
  \frac{2\|(I-\theta^*\theta^{*\top})P\theta^*\|_2}{\nu-2\|P\|_{\mathrm{op}}}.$$
  In the spiked model $x_i=\sqrt\nu\,\xi_i\theta^*+w_i$, with independent
  centered sub-Gaussian $\xi_i$ and $w_i$ of parameter at most one, variance
  one and covariance $I_p$, if $n>p$ and $\nu^{-2}(\nu+1)p/n\le1/128$, then
  with probability at least
  $1-c_1\exp(-c_2n\min(\sqrt\nu\,\delta,\nu\delta^2))$ the leading sample
  eigenvector satisfies
  $\|\hat\theta-\theta^*\|_2\le c_0\sqrt{(\nu+1)\nu^{-2}p/n}+\delta$, with
  universal constants $c_0,c_1,c_2$.
  TauCeti's Davis–Kahan theorem with Weyl's bound gives the sine of the
  angle at most $\|P\|_{\mathrm{op}}/(\nu-\|P\|_{\mathrm{op}})$, and its
  Yu–Wang–Samworth eigenvector bound gives, for a suitable sign,
  $\|\hat\theta-\theta^*\|_2\le2\sqrt2\|P\|_{\mathrm{op}}/\nu$; these are
  bounds of the same type with the full perturbation norm. Its residual
  $\sin\Theta$ theorem in unitarily invariant norms gives the stated form
  by a short argument. Missing are the residual form as stated, uniqueness
  of the leading eigenvector, and the spiked-model bound.

## 104. Bayesian inference and stochastic computation

Mathlib has a measure-theoretic core for Bayesian statistics: the posterior
as a Markov kernel characterized by disintegration of the joint law of
parameter and data, its Radon–Nikodym (Bayes-formula) form, posterior model
probabilities for two models, Bayes risks and Bayes estimators as pointwise
minimizers of posterior expected loss, the law of total variance, Lévy's
upward theorem, change of measure, invariance of a measure under a reversible
kernel, $\varphi$-irreducibility, the Kolmogorov extension theorem, the
maximal ergodic theorem, and relative entropy against a tilted reference,
which is the evidence identity. TauCeti supplies the named parametric
families (Beta, Gamma, Dirichlet with aggregation and one step of stick
breaking, multinomial, Student $t$, multivariate $t$, chi-squared,
conditional multivariate Gaussian laws), a Gamma–Gaussian conjugate pair,
de Finetti's theorem, quantile sampling, Pinsker's inequality, Gaussian
integration by parts in one dimension, Girsanov's theorem for a constant
drift, the coupling inequality, period, and recurrence theory for Markov
chains, the Poincaré and logarithmic Sobolev inequalities as definitions,
and a substantial entropic and Wasserstein layer: existence and uniqueness
of JKO steps under abstract hypotheses, conditional $\mathrm{EVI}$
contraction, McCann's displacement convexity of internal energies, the
Benamou–Brenier formula, the static and dynamic Schrödinger problems with
product-form minimizers and uniqueness of potentials, the continuity
equation with barycentric velocities, relative entropy projections, and
iterative proportional fitting with convergence of its marginals. Statlib
adds differentiability in quadratic mean with the mean-zero score,
contiguity, the $0$–$1$ loss with the posterior-mode Bayes rule, the
squared Hellinger distance, exponential bounds for tests between two simple
hypotheses, and chain rules for the divergence through posteriors and
compositions of kernels. The principal omissions are posterior asymptotics
(Bernstein–von Mises, Laplace approximation, Doob, Schwartz, contraction
rates), nonparametric priors, the convergence theory of Markov chain
samplers, everything that needs stochastic differential equations (Langevin
diffusions and their discretizations, stochastic approximation,
McKean–Vlasov systems, diffusion time reversal, and the Girsanov bound behind
score-based generation), every consequence of functional inequalities for
probability measures, and the limit theory of particle filters.
Metropolis–Hastings invariance and Doob's consistency theorem are selected
although each is a short argument from Mathlib results, indicated in the
assessment.

Sources: [mathematical synopsis](SYNOPSIS104.md); [combined coverage inventory](STRUCTURE104.md).

Observations have density $f(x\mid\theta)$ relative to a dominating measure,
and the prior $\Pi$ has density $\pi$. The **marginal density** is
$m(y)=\int f(y\mid\theta)\pi(\theta)\,d\theta$ and the **posterior density**
is $\pi(\theta\mid y)=f(y\mid\theta)\pi(\theta)/m(y)$ where $m(y)>0$.
$\mathop{\mathrm{KL}}$ is relative entropy, $W_p$ the Wasserstein distance,
and $\|\cdot\|_{\mathrm{TV}}$ total variation with values in $[0,1]$.

For sampling, $V:\mathbb R^d\to\mathbb R$ is twice continuously
differentiable with $\nabla V$ globally Lipschitz and $\int e^{-V}<\infty$,
and $\pi(dx)\propto e^{-V(x)}\,dx$. The **overdamped Langevin diffusion** is
$dX_t=-\nabla V(X_t)\,dt+\sqrt2\,dW_t$, with law $\mu_t$ (density $\rho_t$),
and the **unadjusted Langevin algorithm** is
$X_{(n+1)h}=X_{nh}-h\nabla V(X_{nh})+\sqrt{2h}\,\xi_{n+1}$ with standard
normal $\xi_n$, with law $\hat\mu_{nh}$. Write $\kappa=\beta/\alpha$ when
$\alpha I\preceq\nabla^2V\preceq\beta I$, $\alpha>0$; $V$ is
**$\beta$-smooth** when $\nabla V$ is $\beta$-Lipschitz. The **relative
Fisher information** is $I(\rho\|\pi)=\int\|\nabla\log(\rho/\pi)\|^2\rho$.
A target satisfies a **Poincaré inequality** with constant $C_P$ if
$\mathop{\mathrm{Var}}_\pi f\le C_P\mathbb E_\pi\|\nabla f\|^2$ for smooth $f$,
and a **logarithmic Sobolev inequality** with constant $C_{LS}$ if
$\mathop{\mathrm{KL}}(\mu\|\pi)\le\frac{C_{LS}}2\mathbb E_\mu
\|\nabla\log(d\mu/d\pi)\|^2$ for smooth positive $\mu$. The
**chi-squared divergence** is $\chi^2(\mu\|\pi)=\mathop{\mathrm{Var}}_\pi(d\mu/d\pi)$
for $\mu\ll\pi$, and $+\infty$ otherwise.

### Foundations, parametric Bayesian theory, and nonparametric Bayes

* **104.1. Bernstein–von Mises theorem.** Let independent sampling from a
  model differentiable in quadratic mean at an interior
  $\theta_0\in\mathbb R^k$, with nonsingular Fisher information
  $I(\theta_0)$, give a locally asymptotically normal experiment. Assume a
  prior density continuous and positive at $\theta_0$ and, for each
  $\delta>0$, tests whose type I error and supremum type II error over
  $\|\theta-\theta_0\|\ge\delta$ tend to zero. Let $\hat\theta_n$ be
  efficient,
  $\sqrt n(\hat\theta_n-\theta_0)=I(\theta_0)^{-1}n^{-1/2}
  \sum_i\dot\ell_{\theta_0}(X_i)+o_P(1)$. Then the posterior law of
  $\sqrt n(\theta-\hat\theta_n)$ converges in total variation to
  $N(0,I(\theta_0)^{-1})$, in $P_{\theta_0}$-probability, and the closed
  ball about $\hat\theta_n$ of posterior content $1-\alpha$ has
  $P_{\theta_0}$-coverage tending to $1-\alpha$. Mathlib supplies the
  posterior kernel and the total variation distance. Statlib defines
  differentiability in quadratic mean, proves that the score has mean zero
  at interior points, and defines contiguity with part of the equivalence
  of its forms. Fisher information, local asymptotic normality, and the
  theorem are missing.

* **104.5. Laplace approximation and the BIC.** Let $\Theta\subset\mathbb R^k$
  be open, let $X_1,\ldots,X_n$ be independent with density
  $f(\cdot\mid\theta_0)$, let $\ell_n(\theta)=\sum_i\log f(X_i\mid\theta)$
  be twice continuously differentiable, and let the prior density $\pi$ be
  continuous and positive at $\theta_0$. Suppose that with probability
  tending to one $\ell_n$ has a maximizer $\hat\theta_n\to\theta_0$ in
  probability; that for some $\delta>0$ and positive definite $J$,
  $\sup_{\|\theta-\theta_0\|\le\delta}\|n^{-1}D^2\ell_n(\theta)+J\|\to0$ in
  probability; and that for every $\varepsilon>0$ there is $\eta>0$ with
  $P\bigl(\sup_{\|\theta-\hat\theta_n\|\ge\varepsilon}
  (\ell_n(\theta)-\ell_n(\hat\theta_n))\le-n\eta\bigr)\to1$. With
  $J_n=-D^2\ell_n(\hat\theta_n)$,
  $$\log m(y)=\ell_n(\hat\theta_n)+\log\pi(\hat\theta_n)
  +\frac k2\log(2\pi)-\frac12\log\det J_n+o_P(1),$$
  so $-2\log m(y)=-2\ell_n(\hat\theta_n)+k\log n+O_P(1)$. Mathlib's Gaussian
  integral is the analytic input; the stochastic Laplace expansion is
  missing.

### Credible regions, point nulls, and hierarchical shrinkage

A **highest posterior density region** of level $1-\alpha$ for a posterior
density on $\mathbb R^k$ is a set $C$ with
$\{\pi(\cdot\mid x)>k_\alpha\}\subset C\subset\{\pi(\cdot\mid x)\ge k_\alpha\}$,
where $k_\alpha$ is the largest $k$ for which $\{\pi(\cdot\mid x)\ge k\}$ has
posterior content at least $1-\alpha$.

* **104.10. Highest posterior density regions.** A highest posterior density
  region of posterior content exactly $1-\alpha$ with $k_\alpha>0$ has the
  smallest Lebesgue volume among measurable sets of posterior content at
  least $1-\alpha$. For a posterior on the line symmetric about $c$ and
  nonincreasing in $|\theta-c|$, it may be taken to be the equal-tailed
  interval. The construction is not invariant under reparameterization:
  there are posterior densities on the line and increasing smooth bijections
  $g$ for which $g(C)$ is not a highest posterior density region of the
  image posterior. The volume-minimality needs a bathtub
  (Neyman–Pearson type) lemma for densities, which is absent; no part of
  the entry is stated.

* **104.14. Tweedie's formula and Robbins' estimator.** Let
  $f(x\mid\theta)=h(x)\exp(\theta\cdot x-\psi(\theta))$ on $\mathbb R^k$,
  let the prior $g$ be arbitrary, and let the marginal density $m$ be
  positive and differentiable under the integral sign. Then
  $\mathbb E[\theta\mid X=x]=\nabla\log m(x)-\nabla\log h(x)$. For Poisson
  sampling with any prior on $(0,\infty)$,
  $\mathbb E[\theta\mid X=x]=(x+1)m(x+1)/m(x)$ with $m$ the marginal mass
  function, and for independent $X_1,\ldots,X_n$ with law $m$ and
  $N_n(x)=\#\{i\le n:X_i=x\}$, Robbins' estimator $(x+1)N_n(x+1)/N_n(x)$
  converges almost surely to $\mathbb E[\theta\mid X=x]$ whenever $m(x)>0$.
  The formulas are a differentiation under the integral in the posterior
  density formula of Mathlib, and Robbins' limit follows from the strong
  law applied to the two counts; none of this is stated. TauCeti's
  one-dimensional Gaussian integration by parts is the corresponding
  identity for the normal location model only.

### Nonparametric Bayes, posterior asymptotics, and inverse problems

Let $\mathcal X$ be a standard Borel space and $\alpha$ a finite nonzero
measure on it, with $|\alpha|=\alpha(\mathcal X)$ and $H=\alpha/|\alpha|$. A
random probability measure $P$ is a **Dirichlet process** with parameter
$\alpha$ when $(P(A_1),\ldots,P(A_k))\sim\mathop{\mathrm{Dirichlet}}(\alpha(A_1),
\ldots,\alpha(A_k))$ for every finite measurable partition. Write
$K(P_0,P)=\int p_0\log(p_0/p)$, $V(P_0,P)=\int p_0(\log(p_0/p))^2$, $h$ for
the Hellinger distance with $h^2(P,Q)=\int(\sqrt p-\sqrt q)^2$, and
$N(\varepsilon,\mathcal F,h)$ for covering numbers.

* **104.15. Dirichlet process.** If, given a Dirichlet process $P$ with
  parameter $\alpha$, the $X_1,\ldots,X_n$ are independent with law $P$,
  the posterior of $P$ is a Dirichlet process with parameter
  $\alpha+\sum_i\delta_{X_i}$, and the one-step predictive law is
  $(\alpha+\sum_i\delta_{X_i})/(|\alpha|+n)$. With $V_k$ independent
  $\mathop{\mathrm{Beta}}(1,|\alpha|)$ and $\theta_k$ independent with law
  $H$, independent of the $V_k$, the weights $\pi_k=V_k\prod_{j<k}(1-V_j)$
  make $\sum_k\pi_k\delta_{\theta_k}$ a Dirichlet process with parameter
  $\alpha$ (Sethuraman). TauCeti constructs the finite-dimensional Dirichlet
  laws with their aggregation property, which is the consistency condition
  of a Kolmogorov-type construction, and proves one step of finite stick
  breaking: a Dirichlet vector with positive parameters splits into a Beta
  fraction and an independent Dirichlet remainder. Mathlib proves the
  Kolmogorov extension theorem for projective families of finite measures
  on finite products of second-countable, completely pseudo-metrizable
  spaces, over an arbitrary index set, and TauCeti proves it for projective
  families of probability laws on countably many standard Borel spaces.
  The process, its
  conjugacy, and the infinite stick-breaking representation are missing.

* **104.16. Pólya urn scheme and distinct values.** If $X_1,X_2,\ldots$ are
  conditionally independent with law $P$ given a Dirichlet process $P$ with
  parameter $\alpha$, then $X_1\sim H$ and
  $X_{n+1}\mid X_1,\ldots,X_n\sim(\alpha+\sum_{i\le n}\delta_{X_i})/(|\alpha|+n)$.
  Conversely, a sequence with these predictive laws is exchangeable and its
  de Finetti measure is a Dirichlet process with parameter $\alpha$. If
  $\alpha$ is atomless, the indicators of new values are independent
  Bernoulli with success probabilities $|\alpha|/(|\alpha|+i-1)$, so the
  number $K_n$ of distinct values satisfies
  $\mathbb EK_n=\sum_{i\le n}|\alpha|/(|\alpha|+i-1)\sim|\alpha|\log n$ and
  $K_n/\log n\to|\alpha|$ almost surely. TauCeti proves de Finetti's
  theorem; the urn scheme and its consequences are missing.

* **104.17. Doob's consistency theorem.** Let $\{P_\theta:\theta\in\Theta\}$
  be a dominated model on a standard Borel sample space, with $\Theta$
  Polish, $\theta\mapsto P_\theta(A)$ measurable for every measurable $A$,
  and $\theta\mapsto P_\theta$ injective, and let $\Pi$ be a prior. For
  $X_1,X_2,\ldots$ independent with law $P_\theta$, there is a $\Pi$-null
  set $N$ such that for every $\theta\notin N$ and every neighbourhood $U$
  of $\theta$, the posterior probability of $U$ tends to $1$,
  $P_\theta^\infty$-almost surely. Mathlib's Lévy upward theorem gives
  almost-sure convergence of the posterior probability of $U$ to its
  conditional expectation given the whole sequence; the remaining step is
  that $\theta$ is a measurable function of the sequence, which follows from
  injectivity, the strong law along a countable generating class, and
  measurability of inverses of injective Borel maps. That step and the
  theorem are not stated.

* **104.18. Schwartz's theorem.** Let $\Pi$ be a prior on densities
  relative to a $\sigma$-finite measure, and let $X_1,X_2,\ldots$ be
  independent with density $p_0$. If $\Pi\{P:K(P_0,P)<\varepsilon\}>0$ for
  every $\varepsilon>0$, and for every weak neighbourhood $U$ of $P_0$ there
  are tests of $P_0$ against $U^c$ with type I and type II errors tending to
  zero uniformly over $U^c$, then the posterior probability of $U$ tends to
  $1$ in $P_0$-probability. Mathlib has the divergence with its chain rule,
  and Statlib has exponential bounds for tests between two simple
  hypotheses; tests against the complement of a weak neighbourhood,
  uniformly over a composite alternative, and the theorem are missing.

* **104.19. Contraction rate of Ghosal, Ghosh, and van der Vaart.** Let
  $\varepsilon_n\to0$ with $n\varepsilon_n^2\to\infty$. Suppose that for
  some finite $C$,
  $\Pi\{P:K(P_0,P)\le\varepsilon_n^2,\ V(P_0,P)\le\varepsilon_n^2\}
  \ge e^{-Cn\varepsilon_n^2}$, and that there are sieves $\mathcal F_n$ with
  $\log N(\varepsilon_n/2,\mathcal F_n,h)\le n\varepsilon_n^2$ and
  $\Pi(\mathcal F_n^c)\le e^{-(C+4)n\varepsilon_n^2}$. Then there is
  $M_0<\infty$ such that for every $M\ge M_0$ the posterior probability of
  $\{P:h(P,P_0)\ge M\varepsilon_n\}$ tends to zero in $P_0$-probability.
  Mathlib defines covering numbers, and Statlib defines the squared
  Hellinger distance between measures, normalized as $\frac12h^2$, with its
  comparison with total variation and exponential bounds for tests between
  two simple hypotheses. The moment $V$, the Le Cam–Birgé construction of
  tests from covering numbers, and the theorem are missing.

* **104.20. Linear inverse problems.** Let $A$ be compact and injective
  between separable Hilbert spaces with singular system
  $Ae_j=\kappa_jg_j$, where $(e_j)$ and $(g_j)$ are orthonormal and
  $c_0^{-1}j^{-a}\le\kappa_j\le c_0j^{-a}$ for constants $c_0\ge1$, $a\ge0$.
  Observe $Y=Af+\varepsilon\mathbb W$ for white noise $\mathbb W$,
  equivalently $Y_j=\kappa_jf_j+\varepsilon Z_j$ with $f_j=\langle f,e_j\rangle$
  and independent standard normal $Z_j$.
  For $S^\beta(R)=\{f:\sum_jj^{2\beta}f_j^2\le R^2\}$ and
  $r=2\beta/(2\beta+2a+1)$ there are $0<c\le C$, depending only on
  $a,\beta,R,c_0$, with
  $$c\varepsilon^r\le\inf_{\hat f}\sup_{f\in S^\beta(R)}
  \bigl(\mathbb E_f\|\hat f-f\|^2\bigr)^{1/2}\le C\varepsilon^r\qquad
  (0<\varepsilon\le1).$$
  Under the prior with independent $f_j\sim N(0,j^{-1-2\beta})$, for every
  $M_\varepsilon\to\infty$,
  $\sup_{f_0\in S^\beta(R)}\mathbb E_{f_0}
  \Pi(\|f-f_0\|\ge M_\varepsilon\varepsilon^r\mid Y)\to0$. Only the
  definition of minimax risk is present.

### Monte Carlo and Markov chain Monte Carlo

Let $\pi$ be a target density and $q(x,y)$ the density of a proposal kernel
$q(x,dy)$, and put
$\alpha(x,y)=\min\bigl(1,\pi(y)q(y,x)/(\pi(x)q(x,y))\bigr)$, with
$\alpha(x,y)=1$ when $\pi(x)q(x,y)=0$.

* **104.22. Metropolis–Hastings.** The kernel that proposes
  $Y\sim q(x,\cdot)$ and moves to $Y$ with probability $\alpha(x,Y)$,
  remaining at $x$ otherwise, is reversible with respect to $\pi$ and
  therefore leaves $\pi$ invariant. Mathlib proves that a reversible Markov
  kernel leaves its measure invariant; reversibility is the one computation
  that $\pi(x)q(x,y)\alpha(x,y)=\min(\pi(x)q(x,y),\pi(y)q(y,x))$ is
  symmetric in $(x,y)$, the rejection part being concentrated on the
  diagonal. The kernel and this computation are not formalized.

* **104.24. Central limit theorem for Markov chain Monte Carlo.** Let
  $(X_t)$ be a Markov chain with kernel $P$ and invariant probability $\pi$
  satisfying the drift and minorization condition of Harris's ergodic
  theorem: $PV\le\gamma V+K$ for some $V\ge0$, $\gamma<1$, $K<\infty$, and
  for some $R>2K/(1-\gamma)$ there are $\alpha>0$ and a probability $\nu$
  with $P(x,\cdot)\ge\alpha\nu$ whenever $V(x)\le R$. If $f$ is measurable
  and
  $\mathbb E_\pi|f|^{2+\delta}<\infty$ for some $\delta>0$, then from every
  initial law
  $$\sqrt n\Bigl(n^{-1}\sum_{t=1}^nf(X_t)-\pi(f)\Bigr)
  \Rightarrow N(0,\sigma^2(f)),\qquad
  \sigma^2(f)=\mathop{\mathrm{Var}}_\pi f(X_0)
  +2\sum_{k\ge1}\mathop{\mathrm{Cov}}_\pi\bigl(f(X_0),f(X_k)\bigr),$$
  the series converging absolutely. Mathlib defines $\varphi$-irreducibility
  and proves the central limit theorem for independent identically
  distributed sums only; TauCeti's coupling inequality for Markov chains
  bounds total variation by a meeting probability. Drift and minorization,
  geometric ergodicity, and every Markov-chain limit theorem are missing.

### Convergence of Markov chain samplers

Let $\pi(x)\propto e^{-U(x)}$ on $\mathbb R^d$ with $U$ continuously
differentiable, $M$ positive definite, and $H(x,p)=U(x)+\frac12p^\top M^{-1}p$.
A **leapfrog step** of size $\varepsilon$ maps $(x,p)$ to $(x',p')$ through
$p_{1/2}=p-\frac\varepsilon2\nabla U(x)$, $x'=x+\varepsilon M^{-1}p_{1/2}$,
$p'=p_{1/2}-\frac\varepsilon2\nabla U(x')$; $\Phi$ is the composition of $L$
such steps.

* **104.31. Convergence of Metropolis–Hastings.** If the chain of 104.22 is
  $\pi$-irreducible, it is Harris recurrent, and for every $h\in L^1(\pi)$
  the averages $n^{-1}\sum_{t\le n}h(X_t)$ converge to $\pi(h)$ almost
  surely from every starting point. If it is also aperiodic,
  $P^n(x,\cdot)\to\pi$ in total variation for every $x$. Irreducibility
  holds if $q(x,y)>0$ on the support of $\pi$, and aperiodicity if
  $P(\alpha(X,Y)<1)>0$ for $X\sim\pi$, $Y\sim q(X,\cdot)$. On
  $\mathbb R^d$, if the support of $\pi$ is open and connected, $\pi$ is
  bounded and bounded away from zero on compact subsets of it, and
  $q(x,y)\ge\varepsilon$ whenever $|x-y|<\delta$, the chain is
  $\pi$-irreducible and aperiodic and nonempty compact subsets of the
  support are small. Mathlib has $\varphi$-irreducibility, the trajectory
  law of a chain, and the maximal ergodic theorem for a measure-preserving
  map; TauCeti has the coupling inequality and, on spaces with measurable
  singletons, the period and recurrence of states, which are the inputs of
  the coupling proof for countable chains. Harris recurrence, the ergodic
  theorem for chains, small sets, and total-variation convergence are
  missing.

* **104.32. Independence and random-walk samplers.** For the independence
  sampler with $q(x,y)=g(y)$ and $\pi\le Mg$ on the support of $\pi$,
  $\sup_A|P^n(x,A)-\pi(A)|\le(1-1/M)^n$ for every $x$; if $\pi/g$ is not
  essentially bounded, the chain is not geometrically ergodic. A random-walk
  sampler on $\mathbb R$ with symmetric positive increment density is
  geometrically ergodic only if $\int e^{s|x|}\pi(dx)<\infty$ for some
  $s>0$, and it is geometrically ergodic if $\pi$ is symmetric and
  $\log\pi(x)-\log\pi(y)\ge a|y-x|$ for some $a>0$ and $x_1$ whenever
  $x_1\le x<y$ or $y<x\le-x_1$. No part is present.

* **104.35. Hamiltonian Monte Carlo.** The map $\Phi$ preserves Lebesgue
  measure on $\mathbb R^{2d}$ and is reversible: $\Phi(x,p)=(x',p')$ implies
  $\Phi(x',-p')=(x,-p)$. Drawing $p\sim N(0,M)$, computing
  $(x',p')=\Phi(x,p)$, and moving to $x'$ with probability
  $\min(1,\exp(H(x,p)-H(x',p')))$ gives a kernel that leaves $\pi$
  invariant. Neither the leapfrog map, its volume preservation as a
  composition of shears, nor the Metropolis–Hastings argument with an
  involutive proposal is present.

### Langevin dynamics, sampling, and gradient flows

* **104.37. Invariant measure and gradient-flow structure.** The probability
  $\pi$ is invariant for the overdamped Langevin diffusion, and its marginal
  flow is the $W_2$ gradient flow of $\rho\mapsto\int\rho\log\rho+\int V\,d\rho$,
  solving $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$. None of
  the three libraries has stochastic differential equations. TauCeti proves
  $\mathrm{EVI}$ contraction for solutions whose existence is assumed, and
  McCann's displacement convexity of internal energies, which include the
  entropy, along Wasserstein geodesics; the Fokker–Planck equation and its
  identification as a gradient flow are missing.

* **104.38. Contraction under strong convexity.** If $\nabla^2V\ge mI$ with
  $m>0$, then $W_2(\mu_t,\pi)\le e^{-mt}W_2(\mu_0,\pi)$, and the relative
  entropy is $m$-displacement convex, so $\mathrm{EVI}_m$ contraction
  applies. TauCeti proves that the potential energy of an $m$-strongly convex
  $V$ is $m$-convex along Wasserstein and generalized geodesics, McCann's
  convexity of internal energies, the entropy among them, along Wasserstein
  geodesics, and the contraction of $\mathrm{EVI}$ solutions. Missing are
  the $m$-convexity of the relative entropy as a stated combination,
  convexity of the entropy along generalized geodesics, existence of the
  flow as an $\mathrm{EVI}$ solution, and the synchronous-coupling proof for
  the diffusion.

* **104.39. Iteration complexity of Langevin Monte Carlo.** If
  $\alpha I\preceq\nabla^2V\preceq\beta I$, $\alpha>0$, and
  $\varepsilon\in(0,\sqrt d]$, there are universal $c,C>0$ such that with
  $h=c\varepsilon^2/(\beta d)$ and
  $$N\ge C\frac{\kappa d}{\varepsilon^2}
  \log\Bigl(e+\frac{\alpha W_2^2(\hat\mu_0,\pi)}{\varepsilon^2}\Bigr),$$
  $\sqrt\alpha\,W_2(\hat\mu_{Nh},\pi)\le\varepsilon$, and the mixture
  $\bar\mu=N^{-1}\sum_{j=N+1}^{2N}\hat\mu_{jh}$ satisfies
  $\sqrt{\mathop{\mathrm{KL}}(\bar\mu\|\pi)}\le\varepsilon$. No part is
  present.

* **104.40. Robbins–Monro convergence and averaging.** Let
  $\theta_{n+1}=\theta_n-a_n(h(\theta_n)+M_{n+1})$ with $h(\theta^\star)=0$
  and $(M_n)$ a martingale difference sequence for
  $\mathcal F_n=\sigma(\theta_0,M_1,\ldots,M_n)$. If $h$ is globally
  Lipschitz with $(\theta-\theta^\star)\cdot h(\theta)\ge m\|\theta-\theta^\star\|^2$,
  $m>0$, the steps are positive with $\sum a_n=\infty$, $\sum a_n^2<\infty$,
  the initial state is square-integrable, and
  $\mathbb E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K$, then
  $\theta_n\to\theta^\star$ almost surely. For $a_n=n^{-\alpha}$,
  $1/2<\alpha<1$, if moreover $Dh$ is locally Lipschitz with
  $A=Dh(\theta^\star)$,
  $\mathbb E[M_{n+1}M_{n+1}^\top\mid\mathcal F_n]\to S$ in probability, and
  $\sup_n\mathbb E[\|M_{n+1}\|^{2+\delta}\mid\mathcal F_n]<\infty$ almost
  surely, then $\sqrt n(\bar\theta_n-\theta^\star)\Rightarrow
  N(0,A^{-1}SA^{-\top})$ for $\bar\theta_n=n^{-1}\sum_{k\le n}\theta_k$.
  Mathlib's martingale convergence theorems are the nearest material; the
  Robbins–Siegmund almost-supermartingale theorem, a martingale central
  limit theorem, and both conclusions are missing.

### Entropy and discretization bias

* **104.41. Entropy dissipation of Langevin flow.** If $X_0$ has a
  continuously differentiable density $\rho_0$ with $\rho_0/\pi$ bounded
  above and below by positive constants, then for $t>0$
  $\frac d{dt}\mathop{\mathrm{KL}}(\rho_t\|\pi)=-I(\rho_t\|\pi)$. If $\pi$
  satisfies $\mathop{\mathrm{KL}}(\rho\|\pi)\le I(\rho\|\pi)/(2m)$, then
  $\mathop{\mathrm{KL}}(\rho_t\|\pi)\le e^{-2mt}\mathop{\mathrm{KL}}(\rho_0\|\pi)$;
  strong convexity $\nabla^2V\ge mI$ suffices. TauCeti defines the
  logarithmic Sobolev inequality in its functional form, without
  consequences; relative Fisher information and the diffusion are not
  defined.

### Variational time stepping and functional inequalities

Write $\mathcal F(\rho)=\int\rho\log\rho+\int V\rho$. The **JKO scheme** with
step $\tau>0$ lets $\rho_{k+1}^\tau$ minimize
$\rho\mapsto(2\tau)^{-1}W_2^2(\rho,\rho_k^\tau)+\mathcal F(\rho)$ over
probability densities of finite second moment, with piecewise-constant
interpolation $\rho^\tau(t)=\rho_k^\tau$ for $k\tau\le t<(k+1)\tau$.

* **104.43. Jordan–Kinderlehrer–Otto theorem.** Let $V$ be smooth and
  nonnegative with $\|\nabla V\|\le C(V+1)$, and let $\rho_0$ have finite
  second moment and $\mathcal F(\rho_0)<\infty$ ($e^{-V}$ need not be
  integrable). Every JKO step has a unique minimizer, and as
  $\tau\downarrow0$, $\rho^\tau(t)$ converges weakly in $L^1$ for every
  $t\ge0$, and strongly in $L^1((0,T)\times\mathbb R^d)$, to the unique
  solution of $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$ with
  initial datum $\rho_0$. TauCeti proves existence of JKO steps for abstract
  energies under lower-semicontinuity, coercivity, and tightness hypotheses,
  verifies lower semicontinuity and tight sublevel sets for the Boltzmann
  entropy, and proves uniqueness for energies convex along generalized
  geodesics. Missing are the application to $\mathcal F$, uniqueness for
  $\mathcal F$ (which needs convexity of the entropy along generalized
  geodesics; McCann's theorem in TauCeti gives convexity along geodesics
  only), and convergence of the scheme to the Fokker–Planck equation.

* **104.44. Convergence of the Langevin diffusion under functional
  inequalities.** The Poincaré inequality with constant $C_P$ holds if and
  only if $\chi^2(\mu_t\|\pi)\le e^{-2t/C_P}\chi^2(\mu_0\|\pi)$ for every
  initial law, and the logarithmic Sobolev inequality with constant $C_{LS}$
  holds if and only if
  $\mathop{\mathrm{KL}}(\mu_t\|\pi)\le e^{-2t/C_{LS}}\mathop{\mathrm{KL}}(\mu_0\|\pi)$
  for every initial law; it then gives
  $W_2^2(\mu_t,\pi)\le2C_{LS}e^{-2t/C_{LS}}\mathop{\mathrm{KL}}(\mu_0\|\pi)$.
  The logarithmic Sobolev inequality implies the Poincaré inequality with
  $C_P\le C_{LS}$, and if $V=V_0+\psi$ with $\nabla^2V_0\ge mI$, $m>0$, and
  $\psi$ bounded, both hold with constant at most $e^{\sup\psi-\inf\psi}/m$.
  TauCeti defines the Poincaré and logarithmic Sobolev inequalities for a
  probability measure, proving only monotonicity in the constant, scaling
  under dilations, and the failure of the Poincaré inequality for a
  two-point law. The chi-squared divergence, the implication between the
  two inequalities, the Otto–Villani inequality, and the diffusion are not
  formalized.

### Unadjusted, stochastic-gradient, and Metropolis-adjusted Langevin

The **Metropolis-adjusted Langevin algorithm** uses the unadjusted step as
the proposal of 104.22. The $\frac12$-lazy version of a kernel $K$ is
$\frac12(\delta_x+K(x,\cdot))$; a start $\mu_0$ is $M$-warm if
$\mu_0\le M\pi$; the $\varepsilon$-mixing time is the least $n$ with
$\|\mu_n-\pi\|_{\mathrm{TV}}\le\varepsilon$.

* **104.45. Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  If $\pi$ satisfies the logarithmic Sobolev inequality with constant
  $1/\alpha$ and $V$ is $\beta$-smooth, not necessarily convex, there is a
  universal $C$ such that for $0<h\le\alpha/(4\beta^2)$ and all $N$
  $$\mathop{\mathrm{KL}}(\hat\mu_{Nh}\|\pi)\le
  e^{-\alpha Nh}\mathop{\mathrm{KL}}(\hat\mu_0\|\pi)+C\frac{\beta^2dh}\alpha$$
  (Vempala–Wibisono). If instead $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$,
  there are universal $c,C$ with
  $W_2(\hat\mu_{Nh},\pi)\le e^{-\alpha Nh/2}W_2(\hat\mu_0,\pi)
  +C\beta\sqrt{dh}/\alpha$ for $0<h\le c/(\beta\kappa)$ and all $N$. No part
  is present.

* **104.47. Mixing of Metropolis-adjusted Langevin.** If
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and $0<\varepsilon<1$,
  there are universal $c_0,c_1,c_2>0$ such that, with
  $\Lambda=\log\max\{\kappa,d,M/\varepsilon,c_2\}$, the $\frac12$-lazy MALA
  with step $h=c_0/(\beta d^{1/2}\Lambda^2)$ has $\varepsilon$-mixing time at
  most $c_1\kappa d^{1/2}\Lambda^3$ from every $M$-warm start. Conversely,
  there are universal $c_3,c_4>0$ such that for all $a,b>0$ there is
  $N_{a,b}$ with the property that whenever $d>N_{a,b}$,
  $3\le\kappa\le ad^b$, $M\ge12$, and $h>0$, some such target and some
  $M$-warm start give an $\varepsilon$-mixing time at least
  $c_3\kappa d^{1/2}(\max\{\log\kappa,\log d\})^{-3}\log(c_4/\varepsilon)$.
  No part is present.

### Kinetic Langevin dynamics

The **kinetic Langevin diffusion** with friction $\gamma>0$ is
$dX_t=P_t\,dt$, $dP_t=-\nabla V(X_t)\,dt-\gamma P_t\,dt+\sqrt{2\gamma}\,dW_t$
on $\mathbb R^{2d}$, with law $\boldsymbol\pi_t$.

* **104.48. Invariance, contraction, and hypocoercivity.** The probability
  $\boldsymbol\pi=\pi\otimes N(0,I)$ is invariant, and the process is not
  reversible. If $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and
  $\gamma\ge\sqrt{2\beta}$, two copies driven by the same Brownian motion
  satisfy $|||\Delta_t|||\le e^{-\alpha t/\gamma}|||\Delta_0|||$ with
  $|||(x,p)|||^2=\|x\|^2+\|x+2p/\gamma\|^2$. If $\pi$ satisfies a Poincaré
  inequality with constant $1/\alpha$, $V$ is $\beta$-smooth, and
  $\gamma=c_0\sqrt\beta$, the relative density
  $f_t=d\boldsymbol\pi_t/d\boldsymbol\pi-1$ satisfies
  $$\|f_t\|^2+\tfrac1\beta\|\nabla_xf_t\|^2+\|\nabla_pf_t\|^2
  \le Ce^{-c\alpha t/\sqrt\beta}\bigl(\|f_0\|^2+\tfrac1\beta\|\nabla_xf_0\|^2
  +\|\nabla_pf_0\|^2\bigr)$$
  in $L^2(\boldsymbol\pi)$, with $c,C$ depending only on $c_0$. If instead
  $\pi$ satisfies a logarithmic Sobolev inequality with constant $1/\alpha$,
  with the same $\gamma$, there are real constants $a,b,c_1$ and a universal
  $c'>0$ such that
  $$\mathcal L_t=\mathop{\mathrm{KL}}(\boldsymbol\pi_t\|\boldsymbol\pi)
  +\mathbb E_{\boldsymbol\pi_t}\Bigl\langle\nabla\log\frac{\boldsymbol\pi_t}
  {\boldsymbol\pi},\Bigl(\begin{pmatrix}a/\beta&b/\sqrt\beta\\
  b/\sqrt\beta&c_1\end{pmatrix}\otimes I_d\Bigr)\nabla\log\frac{\boldsymbol\pi_t}
  {\boldsymbol\pi}\Bigr\rangle$$
  satisfies $\mathcal L_t\le e^{-c'\alpha t/\sqrt\beta}\mathcal L_0$. No part
  is present.

### The ordinary differential equation method

For the recursion of 104.40 the **limiting equation** is
$\dot\theta=-h(\theta)$ with flow $\Phi_t$. A compact set is **invariant** if
$\Phi_t(A)=A$ for all real $t$. It is **internally chain transitive** if, in
addition, for all $x,y\in A$ and all $\varepsilon,T>0$ there are points
$x_0,\ldots,x_n=y$ in $A$ with $\|x_0-x\|<\varepsilon$ such that the
trajectory from each $x_i$ enters the $\varepsilon$-neighbourhood of
$x_{i+1}$ after a time at least $T$.

* **104.49. Benaïm's limit-set theorem.** Suppose $h$ is globally Lipschitz,
  $a_n>0$, $\sum a_n=\infty$, $\sum a_n^2<\infty$, $(M_n)$ is a martingale
  difference sequence for $\mathcal F_n=\sigma(\theta_0,M_1,\ldots,M_n)$ with
  $\mathbb E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K(1+\|\theta_n\|^2)$, and
  $\sup_n\|\theta_n\|<\infty$ almost surely. Then almost surely $\theta_n$
  converges to a, possibly sample-dependent, compact connected internally
  chain transitive invariant set of the limiting equation. If the only such
  sets are isolated equilibria, $\theta_n$ converges almost surely to a
  possibly random equilibrium. With $t_n=\sum_{k<n}a_k$ and $\bar\theta$ the
  piecewise linear interpolation, for every $T>0$, almost surely,
  $\lim_{s\to\infty}\sup_{0\le u\le T}\|\bar\theta(s+u)-\Phi_u(\bar\theta(s))\|=0$.
  Mathlib has flows of Lipschitz equations; asymptotic pseudotrajectories,
  chain transitivity, and the theorem are missing.

### Particle methods, data assimilation, and training dynamics

The **McKean–Vlasov** process solves
$d\bar X_t=b(\bar X_t,\mathop{\mathrm{Law}}(\bar X_t))\,dt+dW_t$; the
$N$-particle system evaluates the drift at the empirical measure of the
particles. A **particle filter** approximates the filter $\eta_t$ of a
hidden Markov model by weighted particles resampled according to the
likelihood weights.

* **104.51. Propagation of chaos.** Assume a drift globally Lipschitz in
  position and in $W_1$ of the measure, independent Brownian drivers, and
  independent identically distributed initial states of finite second
  moment, independent of the drivers. Then the limiting equation and the
  particle systems have unique strong solutions, and for every $T<\infty$
  and fixed $k$ the joint path law on $[0,T]$ of the first $k$ particles
  converges weakly on $C([0,T];\mathbb R^{dk})$ to the $k$-fold product of
  the McKean–Vlasov path law. TauCeti's empirical Wasserstein convergence
  and Kantorovich–Rubinstein duality are natural inputs; stochastic
  differential equations and the theorem are missing.

* **104.53. Mean-field training.** For $f_\rho(x)=\int\phi(x,\theta)\rho(d\theta)$
  and $\mathcal R(\rho)=\frac12\mathbb E(Y-f_\rho(X))^2$ with
  $\mathbb EY^2<\infty$, put $V(\theta)=\mathbb E[Y\phi(X,\theta)]$,
  $U(\theta,\theta')=\mathbb E[\phi(X,\theta)\phi(X,\theta')]$, and
  $\Psi(\theta;\rho)=-V(\theta)+\int U(\theta,\theta')\rho(d\theta')$, and
  assume $\nabla V$ and $\nabla_\theta U$ bounded and globally Lipschitz.
  For $N$ particles with empirical measure $\rho_N$, the time-scaled
  gradient flow is $\dot\theta_i=-\nabla_\theta\Psi(\theta_i;\rho_N)$, and if
  the initial particles are independent with law $\rho_0$ of finite first
  moment, then $\sup_{t\le T}W_1(\rho_N(t),\rho_t)\to0$ almost surely for
  every $T<\infty$, where $\rho_t$ is the unique weak solution of
  $\partial_t\rho=\nabla\cdot(\rho\nabla_\theta\Psi(\cdot;\rho))$ with
  datum $\rho_0$. The algebraic expansion of $\mathcal R$ is elementary;
  the well-posedness of the nonlinear continuity equation and the mean-field
  limit are missing.

* **104.55. Consistency of the particle filter.** If the observation
  potentials are bounded and bounded away from zero, then for the bootstrap
  particle filter with multinomial resampling, at each fixed time and for
  every bounded measurable $f$, the particle estimate of $\eta_t(f)$
  converges in probability to $\eta_t(f)$ as the number of particles tends
  to infinity. Hidden Markov models, their filters, and particle systems are
  not defined in any of the three libraries.

### Quantitative chaos and nonlinear filtering

* **104.56. A quantitative interaction model.** Let
  $b(x,\mu)=b_0(x)+\int K(x,y)\mu(dy)$ with $b_0$ globally Lipschitz and $K$
  bounded and globally Lipschitz, and couple the particles with independent
  nonlinear copies $\bar X^i$ using the same initial values and Brownian
  motions. For independent identically distributed initial values of finite
  second moment and every finite $T$,
  $\mathbb E\sup_{t\le T}\|X_t^{i,N}-\bar X_t^i\|^2\le C_T/N$, with $C_T$
  depending only on $T$, the Lipschitz constants, and $\sup|K|$. The
  coupling argument needs stochastic differential equations, which are
  absent.

* **104.58. Unbiased particle likelihood.** For a hidden Markov model with
  likelihoods $G_s(x)=p(y_s\mid x)>0$ and data likelihood $Z_t$, a bootstrap
  particle filter with conditionally unbiased resampling and predicted
  particles $X_s^{i,-}$ gives
  $\hat Z_t=\prod_{s=1}^t\bigl(N^{-1}\sum_{i=1}^NG_s(X_s^{i,-})\bigr)$ with
  $\mathbb E\hat Z_t=Z_t$, the observations being fixed. With multinomial
  resampling and potentials bounded and bounded away from zero, the mean
  squared error of the particle estimate of $\eta_t(f)$ is at most
  $C_t\|f\|_\infty^2/N$, with $C_t$ independent of $N$ and $f$. Mathlib's
  posterior kernel and its composition rule describe one
  prediction–correction step; the particle system and both statements are
  missing.

### Fluctuations, stability, and resampling of particle filters

Let $(X_n)$ be a Markov chain with initial law $\eta_0$ and kernels $M_n$,
and $G_n>0$ bounded potentials, with
$\gamma_n(f)=\mathbb E[f(X_n)\prod_{p<n}G_p(X_p)]$, $\eta_n=\gamma_n/\gamma_n(1)$,
and $Q_{p,n}f(x)=\mathbb E[f(X_n)\prod_{q=p}^{n-1}G_q(X_q)\mid X_p=x]$. The
**bootstrap particle model** draws generation $0$ from $\eta_0$ and
generation $n$ independently from
$\sum_iG_{n-1}(\xi_{n-1}^i)M_n(\xi_{n-1}^i,\cdot)/\sum_iG_{n-1}(\xi_{n-1}^i)$;
$\eta_n^N$ is its empirical measure and $\gamma_n^N(1)=\prod_{p<n}\eta_p^N(G_p)$.

* **104.59. Central limit theorem for Feynman–Kac particle models.** If
  $\inf_xG_p(x)>0$ for every $p$, then for bounded measurable $f$ and fixed
  $n$, as $N\to\infty$,
  $$\sqrt N\bigl(\eta_n^N(f)-\eta_n(f)\bigr)\Rightarrow
  N\Bigl(0,\sum_{p=0}^n\frac{\eta_p([Q_{p,n}(f-\eta_nf)]^2)}{\eta_p(Q_{p,n}1)^2}\Bigr),$$
  $$\sqrt N\Bigl(\frac{\gamma_n^N(1)}{\gamma_n(1)}-1\Bigr)\Rightarrow
  N\Bigl(0,\sum_{p=0}^n\Bigl[\frac{\eta_p((Q_{p,n}1)^2)}{\eta_p(Q_{p,n}1)^2}-1\Bigr]\Bigr).$$
  No part is present.

* **104.60. Uniform-in-time particle approximation.** If there are
  $\varepsilon_G,\varepsilon_M\in(0,1]$ with $G_n(x)\ge\varepsilon_GG_n(x')$
  and $M_n(x,\cdot)\ge\varepsilon_MM_n(x',\cdot)$ for all $n,x,x'$, then for
  every $p\ge1$ there is $c_p<\infty$ with
  $$\sup_{n\ge0}\sup_{\mathop{\mathrm{osc}}(f)\le1}
  \sqrt N\bigl(\mathbb E|\eta_n^N(f)-\eta_n(f)|^p\bigr)^{1/p}
  \le\frac{c_p}{\varepsilon_M^2\varepsilon_G}.$$
  No part is present.

### Score matching, diffusion generative models, and Schrödinger bridges

Let the forward diffusion on $[0,T]$ be $dX_t=f(t,X_t)\,dt+g(t)\,dW_t$ with
$g(t)$ invertible, $p_t$ the law (and density) of $X_t$, and $Y_t=X_{T-t}$
its time reversal.

* **104.63. Anderson's time reversal and the probability-flow equation.**
  Suppose $f$ is continuous and globally Lipschitz in $x$ uniformly in $t$,
  $g$ is continuous, and each $p_t$, $0<t\le T$, has a positive density with
  $\int_{t_0}^T\int_{\|x\|\le r}(p_t^2+\|\nabla p_t\|^2)\,dx\,dt<\infty$ for
  all $t_0\in(0,T)$ and $r>0$. Then (Haussmann–Pardoux) there is a Brownian
  motion $\bar W$ with
  $$dY_t=\bigl(-f(T-t,Y_t)+g(T-t)g(T-t)^\top\nabla\log p_{T-t}(Y_t)\bigr)dt
  +g(T-t)\,d\bar W_t\quad\text{on }[0,T).$$
  The laws $q_t=p_{T-t}$ solve $\partial_tq_t+\nabla\cdot(q_tu_t)=0$ with
  $u_t=-f(T-t,\cdot)+\frac12gg^\top(T-t)\nabla\log p_{T-t}$, and if $u_t$ is
  globally Lipschitz in $x$, uniformly on $[0,T']$ for every $T'<T$, and
  $X_0$ has finite second moment, the flow $\dot Z_t=u_t(Z_t)$ with
  $Z_0\sim p_T$ has law $p_{T-t}$ for $t<T$. The ODE trajectories are
  continuous on $[0,T)$ and solve the equation on each compact subinterval.
  Stochastic calculus and time
  reversal of diffusions are absent from all three libraries; TauCeti's
  continuity equation is the only supporting material.

* **104.64. Score matching.** Let $p$ be positive and continuously
  differentiable on $\mathbb R^d$ and $q_\theta$ twice continuously
  differentiable, with $\|\nabla\log p\|^2$, $\|\nabla\log q_\theta\|^2$, and
  $|\Delta\log q_\theta|$ $p$-integrable and $p\nabla\log q_\theta$
  Lebesgue integrable. Then
  $\int(\frac12\|\nabla\log q_\theta\|^2+\Delta\log q_\theta)\,dp$ equals
  $\frac12\int\|\nabla\log q_\theta-\nabla\log p\|^2\,dp$ up to a constant
  free of $\theta$. If $Y=X+\sigma\varepsilon$ with independent standard
  normal $\varepsilon$, then $\mathbb E[-\varepsilon/\sigma\mid Y]=
  \nabla\log p_\sigma(Y)$, and among measurable $s$ with
  $\mathbb E\|s(Y)\|^2<\infty$ the objective
  $\mathbb E\|s(Y)+\varepsilon/\sigma\|^2$ is minimized exactly by
  $s=\nabla\log p_\sigma$, $p_\sigma$-almost everywhere. The first part is
  an integration by parts on $\mathbb R^d$ under integrability hypotheses;
  the second needs Gaussian smoothing of densities and the least-squares
  characterization of conditional expectation as a stated minimization.
  Neither is present; TauCeti's one-dimensional Gaussian integration by
  parts is the scalar form of the Stein identity behind the second part,
  and its multivariate form is absent.

* **104.68. Score error and total variation.** Under the first hypotheses
  of 104.63, let $P$ be the path law of the exact reversal, let $s_t(x)$ be
  measurable in $(t,x)$ and globally Lipschitz in $x$ uniformly in $t$, and
  let $Q$ be the law of the reverse equation with $s$ in place of the score
  and initial law $\eta$. If $\mathop{\mathrm{KL}}(p_T\|\eta)<\infty$ and
  $\sup_{t,x}\|g(t)^\top(s_t(x)-\nabla\log p_t(x))\|<\infty$, then
  $$\mathop{\mathrm{KL}}(P\|Q)\le\mathop{\mathrm{KL}}(p_T\|\eta)
  +\frac12\int_0^T\mathbb E_{p_t}\|g(t)^\top(s_t-\nabla\log p_t)\|^2\,dt,$$
  and the total variation distance between $p_0$ and the endpoint law of
  $Q$ is at most $\sqrt{\mathop{\mathrm{KL}}(P\|Q)/2}$. Mathlib's
  data-processing inequality and TauCeti's Pinsker inequality give the last
  step. TauCeti proves Girsanov's theorem for a constant drift only, and
  stochastic integrals are absent; the Girsanov bound is missing.

### Training objectives and discrete-time samplers

For the variance-exploding process $dX_t=dW_t$, $X_0\sim\pi$, put
$\pi_t=\pi*N(0,tI)$. For $0=\tau_0<\cdots<\tau_N<T$ with steps
$h_n=\tau_{n+1}-\tau_n$, $\delta=T-\tau_N$, and a score estimate $\hat s_t$,
the **DDPM sampler** starts from $\hat X_0\sim N(0,TI)$ and sets
$\hat X_{\tau_{n+1}}=\hat X_{\tau_n}+h_n\hat s_{T-\tau_n}(\hat X_{\tau_n})
+\sqrt{(T-\tau_{n+1})h_n/(T-\tau_n)}\,\xi_{n+1}$ with independent standard
normal $\xi_n$.

* **104.75. Convergence of diffusion sampling under a second-moment
  assumption.** Suppose only $m_2^2=\mathbb E_\pi\|X\|^2<\infty$ and
  $h_n\le\bar h(T-\tau_n)$ with $\bar h\le1/2$, and put
  $\varepsilon_{\mathrm{sc}}^2=\sum_nh_n\mathbb E_{\pi_{T-\tau_n}}
  \|\hat s_{T-\tau_n}-\nabla\log\pi_{T-\tau_n}\|^2$. Then the law $\hat\pi$
  of $\hat X_{\tau_N}$ satisfies
  $$\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\le\frac{m_2^2}{2T}
  +4\varepsilon_{\mathrm{sc}}^2+2\bar hd\bigl(1+\log(T/\delta)\bigr).$$
  Given $0<\delta<T$ and $\bar h\le1/2$, let $N$ be the least integer with
  $(1-\bar h)^NT\le\delta$, and take $h_n=\bar h(T-\tau_n)$ for $n<N-1$ and
  $h_{N-1}=T-\tau_{N-1}-\delta$; these steps satisfy the hypothesis and
  $N\le1+\bar h^{-1}\log(T/\delta)$. Hence, for $0<\varepsilon^2\le d$,
  taking $T=m_2^2/\varepsilon^2>\delta$ and
  $\bar h=\varepsilon^2/(2d(1+\log(T/\delta)))$ gives
  $\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\le\frac32\varepsilon^2
  +4\varepsilon_{\mathrm{sc}}^2$ with
  $N\le1+2d\varepsilon^{-2}(1+\log(T/\delta))\log(T/\delta)$ steps. No
  part is present. The chain rule for relative entropy is available in
  TauCeti for a single composition product, and Statlib proves the chain
  rule for the conditional divergence of a composition of two kernels,
  the inductive step of the chain rule along a Markov chain; the
  $N$-step identity is not stated.

### Marginal-preserving dynamics and bridge iterations

For path measures $Q,R$ on $C([0,T];\mathbb R^d)$, $Q_0,Q_T$ are the endpoint
laws and $Q^x$ a regular conditional law given $X_0=x$. **Iterative
proportional fitting** sets $P^0=R$ and alternately takes the half-bridge,
the minimizer of $\mathop{\mathrm{KL}}(\cdot\|P^k)$ with one prescribed
endpoint law, with terminal law $\mu_T$ and with initial law $\mu_0$.

* **104.76. A family of diffusions with prescribed marginals.** Let $\mu_t$,
  $t\in[0,1]$, be smooth positive densities solving
  $\partial_t\mu_t+\nabla\cdot(\mu_tv_t)=0$, and let $\epsilon_t\ge0$ be
  continuous. Then $\mu_t$ solves the Fokker–Planck equation of
  $dX_t=(v_t+\epsilon_t\nabla\log\mu_t)(X_t)\,dt+\sqrt{2\epsilon_t}\,dW_t$.
  If the drift $b_t=v_t+\epsilon_t\nabla\log\mu_t$ is jointly Borel
  measurable on $[0,1]\times\mathbb R^d$, globally Lipschitz in $x$,
  uniformly in $t\in[0,1]$, and
  $\int_0^1\int\|b_t\|\,d\mu_t\,dt<\infty$, then a continuous solution of
  the displayed SDE with $\int_0^1\|b_t(X_t)\|\,dt<\infty$ almost surely
  and $X_0\sim\mu_0$ has $X_t\sim\mu_t$ for all $t$; the same holds in
  reverse time with drift
  $v_t-\epsilon_t\nabla\log\mu_t$ under the same hypotheses on that drift.
  For a stochastic interpolant $X_t=I_t(X_0,X_1)+\gamma_tZ$ with
  $I_0(x_0,x_1)=x_0$, $I_1(x_0,x_1)=x_1$, $\gamma_0=\gamma_1=0$, $\gamma_t>0$
  on $(0,1)$, $I$ and $\gamma$ continuously differentiable in $t$ with
  $\int_0^1\mathbb E\|\partial_tI_t(X_0,X_1)\|^2dt<\infty$ and
  $\int_0^1\dot\gamma_t^2dt<\infty$, and $Z$ standard normal independent of
  the coupling, the law $\mu_t$ of $X_t$ has a smooth positive density for
  $0<t<1$, and $v_t(x)=\mathbb E[\partial_tI_t+\dot\gamma_tZ\mid X_t=x]$ and
  $\nabla\log\mu_t(x)=-\gamma_t^{-1}\mathbb E[Z\mid X_t=x]$. TauCeti's
  continuity equation with barycentric velocities is supporting; the
  Fokker–Planck theory and the uniqueness needed to identify the laws of
  the diffusions are missing.

* **104.77. Half-bridges and iterative proportional fitting.** If
  $\mathop{\mathrm{KL}}(\mu_0\|P_0)<\infty$, the unique half-bridge with
  initial law $\mu_0$ is $\frac{d\mu_0}{dP_0}(X_0)\cdot P$, with value
  $\mathop{\mathrm{KL}}(\mu_0\|P_0)$; if $\mathop{\mathrm{KL}}(\mu_T\|P_T)<\infty$,
  the unique half-bridge with terminal law $\mu_T$ is
  $\frac{d\mu_T}{dP_T}(X_T)\cdot P$.
  Every iterate has the form $f_k(X_0)g_k(X_T)\cdot R$ and its endpoint
  couplings are the Sinkhorn iterates for $R_{0T}$. If $P^*$ is the
  Schrödinger bridge with $\mathop{\mathrm{KL}}(P^*\|R)<\infty$, then
  $\mathop{\mathrm{KL}}(P^*\|P^k)=\mathop{\mathrm{KL}}(P^*\|P^{k+1})
  +\mathop{\mathrm{KL}}(P^{k+1}\|P^k)$, so $\mathop{\mathrm{KL}}(P^*\|P^k)$
  is nonincreasing, $\sum_k\mathop{\mathrm{KL}}(P^{k+1}\|P^k)\le
  \mathop{\mathrm{KL}}(P^*\|R)$, and the endpoint marginals converge to
  $\mu_0,\mu_T$ in relative entropy and in total variation. If
  $R_{0T}\ll\mu_0\otimes\mu_T$ with density $e^{-c}$, $c$ bounded below and
  $\int e^{rc}\,d(\mu_0\otimes\mu_T)<\infty$ for some $r>1$, then
  $\mathop{\mathrm{KL}}(P^*\|P^k)\to0$ and the endpoint couplings converge in
  total variation to that of $P^*$. TauCeti proves the half-bridge as a
  general entropy projection, and for the static iteration the telescoping
  identity, monotonicity, and convergence of the marginal errors. Missing
  are the iteration on path space and the convergence of the couplings
  under the integrability condition.

## 105. Linear models, multivariate analysis, experimental design, and causal inference

None of the three libraries defines a linear model, a least-squares or
generalized linear-model estimator, an analysis-of-variance decomposition, a
design, an assignment mechanism or potential-outcome model with a probability
structure, or a graphical Markov property. Mathlib supplies the
linear-algebraic and probabilistic infrastructure: orthogonal projection as the
nearest-point map, Schur complements, the Woodbury identity, the trace of a
projection, the independence of jointly Gaussian blocks with vanishing
cross-covariance, the tilted-measure formulas for the mean and variance of a
natural exponential family, conditional independence, regular conditional
distributions, kernel composition, the scalar central limit theorem with the
Cramér–Wold device and Slutsky's theorem, and Fisher's inequality for
balanced incomplete block designs with $\lambda=1$ through finite
configurations. TauCeti adds Gaussian conditioning with positive-semidefinite
covariance and affine images, the chi-squared laws and joint independence of
squared lengths of projections of a standard Gaussian vector onto orthogonal
subspaces, the noncentral chi-squared law with the law of $\|Y\|^2$ for
$Y\sim N_n(m,I_n)$, the noncentral $F$ law, the moment-generating function
of a Gaussian quadratic form, the chi-squared, Student, Fisher and Beta laws
as laws of the classical constructions, a developed Wishart theory (Gram
representation, density, congruence, marginals, moments, transforms, the
Bartlett decomposition, the determinant law, and the Schur-complement law
for a block of size one), the von Mises–Fisher density and mean, the Ky Fan
inequality with its attainment and the Courant–Fischer theorem, principal
cosines, concavity of $(\det A)^{1/n}$, and sampling without replacement.
Statlib supplies a notation for potential responses, without probability
structure, and the binary Bayes test. The principal omissions
are the normal theory of the linear model with Cochran's theorem and the
laws of general quadratic forms, generalized-linear-model and quantile-regression
asymptotics, the classical multivariate sampling theory and tests, graphical
Markov properties, optimal and combinatorial design, finite-population
survey sampling, and the whole of potential-outcome and graphical causal inference. The Gauss–Markov theorem,
the normal sampling theory of the linear model and its exact $F$ tests,
the randomization test, Neyman's variance formula, and the identification
formulas of items 47, 48 and 50 are selected although each follows from
library results by a short argument, which is indicated.

Sources: [mathematical synopsis](SYNOPSIS105.md); [combined coverage inventory](STRUCTURE105.md).

In the linear model, $Y$ is an $n$-vector of responses with mean $X\beta$,
where $X$ is a fixed $n\times p$ design matrix of rank $r$, and $P$ is the
orthogonal projection onto the column space of $X$. For $Z\sim N_k(m,I_k)$
the law of $\|Z\|^2$ is the **noncentral chi-squared law** on $k$ degrees of
freedom with noncentrality $\|m\|^2$; the central law has $m=0$. The
**Wishart law** $W_p(n,\Sigma)$ is the law of $\sum_{i=1}^nZ_iZ_i^\top$ for
independent $Z_i\sim N_p(0,\Sigma)$. Write $\Rightarrow$ for convergence in
distribution and $\to_P$ for convergence in probability.

### Regression, generalised linear models, and mixtures

An **exponential dispersion family** has density
$\exp\bigl((y\theta-b(\theta))/a(\varphi)+c(y,\varphi)\bigr)$ with respect to a
dominating measure. A **generalised linear model** specifies
$g(\mu_i)=x_i^\top\beta=\eta_i$ for a link $g$; with $a(\varphi)=\varphi$,
$\mathop{\mathrm{Var}}(Y_i)=\varphi V(\mu_i)$, and the weights are
$W=\mathop{\mathrm{diag}}\bigl((d\mu_i/d\eta_i)^2/V(\mu_i)\bigr)$. The
**check function** of order $\tau\in(0,1)$ is $\rho_\tau(u)=u(\tau-1_{\{u<0\}})$.

* **105.1. Gauss–Markov theorem.** Assume $\mathbb E\varepsilon=0$ and
  $\mathop{\mathrm{Cov}}(\varepsilon)=\sigma^2I_n$. Among linear unbiased
  estimators of an estimable functional $c^\top\beta$, the least-squares
  estimator has the smallest variance. If $X$ has full column rank,
  $\sigma^2(X^\top X)^{-1}$ is the Loewner minimum of the covariances of
  linear unbiased estimators of $\beta$. None of the three libraries defines
  the linear model or its estimators. The theorem follows from Mathlib's orthogonal
  projection by a short argument: if $a^\top Y$ is unbiased for
  $c^\top\beta$, then $(Pa)^\top Y$ is the least-squares estimator of
  $c^\top\beta$ and $\sigma^2\|a\|^2\ge\sigma^2\|Pa\|^2$; the Loewner form
  follows by applying this to every functional $u^\top\beta$.

* **105.2. Normal sampling theory.** If $\varepsilon\sim N(0,\sigma^2I_n)$,
  then $\|PY\|^2/\sigma^2$ is noncentral chi-squared on $r$ degrees of
  freedom with noncentrality $\|P\mu\|^2/\sigma^2$, where $\mu=\mathbb EY$,
  and it is independent of $\|(I-P)Y\|^2$; the residual sum of squares
  $\|(I-P)Y\|^2/\sigma^2$ is chi-squared on $n-r$ degrees of freedom. When
  $X$ has full column rank, the least-squares estimator is normal with mean
  $\beta$ and covariance $\sigma^2(X^\top X)^{-1}$ and is independent of the
  residual sum of squares. TauCeti proves the case $\mu=0$, $\sigma=1$:
  for a standard Gaussian vector, the squared lengths of its projections
  onto pairwise orthogonal subspaces are independent chi-squared variables
  on the respective dimensions, so $\|PY\|^2\sim\chi^2_r$ is independent of
  $\|(I-P)Y\|^2\sim\chi^2_{n-r}$. TauCeti also defines the noncentral
  chi-squared law, proves that a sum of squares of independent $N(m_i,1)$
  variables, and the squared norm of an $N_n(m,I_n)$ vector, have that law
  with noncentrality $\sum_im_i^2$, respectively $\|m\|^2$, and proves that
  affine images of Gaussian vectors are Gaussian. Not stated are the
  noncentral law of the projected sum $\|PY\|^2/\sigma^2$ for general $\mu$
  and $\sigma$, its independence of the residual sum of squares, and the law
  of the least-squares estimator; they follow by a short argument, writing
  $Y=\mu+\sigma Z$ and expanding the projection of $Z$ in an orthonormal
  basis of the column space.

* **105.3. Asymptotics of the generalised linear model.** For independent
  responses from an exponential dispersion family with $a(\varphi)=\varphi$,
  a twice differentiable link with $g'>0$, and means in the interior of the
  mean space, the Fisher information for $\beta$ is $\varphi^{-1}X^\top WX$.
  Suppose that the pairs $(x_i,Y_i)$ are independent and identically
  distributed, that the model for one pair satisfies the regularity
  hypotheses of SYNOPSIS102, item 3, at the true $\beta$, and that
  $J=\mathbb E[x_1x_1^\top w(x_1)]$ is nonsingular, where
  $w(x)=(d\mu/d\eta)^2/V(\mu)$ at $\eta=x^\top\beta$. Then a consistent root
  $\hat\beta$ of the likelihood equations satisfies
  $\sqrt n(\hat\beta-\beta)\Rightarrow N(0,\varphi J^{-1})$, and
  $\hat\varphi^{-1/2}J^{1/2}\sqrt n(\hat\beta-\beta)\Rightarrow N(0,I_p)$ for
  every consistent $\hat\varphi$. For two nested such models with
  $\varphi$ known, the difference of the scaled deviances is the
  likelihood-ratio statistic and, under the smaller model and the
  hypotheses of SYNOPSIS102, item 11, converges in distribution to
  chi-squared on the difference of the dimensions. Mathlib's tilted-measure
  identities give $\mathbb EY=b'(\theta)$ and
  $\mathop{\mathrm{Var}}Y=b''(\theta)$ in the one-parameter case
  $a(\varphi)=1$; the dispersion family, links, Fisher information, and
  likelihood asymptotics are absent.

* **105.5. Quantile regression.** Let $Y_1,Y_2,\ldots$ be independent with
  fixed regressors $x_i\in\mathbb R^p$, and suppose the $\tau$-quantile of
  $Y_i$ is $\xi_i=x_i^\top\beta_\tau$. Assume that $Y_i$ has a density
  $f_i$, that the values $f_i(\xi_i)$ are bounded away from $0$ and
  $\infty$, that the $f_i$ are equicontinuous at the points $\xi_i$, that
  $n^{-1}\sum_{i\le n}x_ix_i^\top\to D_0$ and
  $n^{-1}\sum_{i\le n}f_i(\xi_i)x_ix_i^\top\to D_1$ with $D_0,D_1$ positive
  definite, and that $\max_{i\le n}\|x_i\|/\sqrt n\to0$. Then every minimizer
  $\hat\beta_\tau$ of $\sum_{i\le n}\rho_\tau(Y_i-x_i^\top\beta)$ satisfies
  $$\sqrt n\,(\hat\beta_\tau-\beta_\tau)
  \Rightarrow N\bigl(0,\,\tau(1-\tau)\,D_1^{-1}D_0D_1^{-1}\bigr).$$
  TauCeti has the quantile function of a real law with its Galois
  characterization; the check-function characterization of quantiles and
  all of quantile regression are absent.

* **105.6. Finite normal mixtures.** A finite mixture of nondegenerate
  Gaussian distributions on $\mathbb R^d$, with distinct component
  parameters and strictly positive weights, is identifiable up to
  permutation of the component labels. With at least two components and
  unconstrained component covariances, the likelihood is unbounded: a
  component mean placed at an observation, with that component's variance
  sent to zero, drives the likelihood to infinity. TauCeti defines finite
  multivariate Gaussian mixture laws and densities and computes their
  moments. Identifiability and the unboundedness of the likelihood are
  not stated; identifiability needs an additional analytic argument.

### Linear-model reductions and diagnostics

* **105.10. Exact tests of nested linear models.** Let $P_0,P_1$ project onto
  nested model spaces of dimensions $r_0<r_1<n$. Under the smaller model and
  independent $N(0,\sigma^2)$ errors,
  $$\frac{\|(P_1-P_0)Y\|^2/(r_1-r_0)}
  {\|(I-P_1)Y\|^2/(n-r_1)}\sim F_{r_1-r_0,n-r_1},$$
  the numerator and denominator sums of squares, divided by $\sigma^2$,
  being independent chi-squared variables. Under the larger model the
  numerator has noncentrality $\|(P_1-P_0)X\beta\|^2/\sigma^2$, and a single
  estimable contrast gives the square of the Student $t$ statistic. TauCeti
  proves that the ratio of independent chi-squared variables, each divided
  by its degrees of freedom, has the Fisher law, the corresponding Student
  construction, and the noncentral $F$ law of the ratio when the numerator
  is noncentral. None of the three libraries states the test. Under the
  smaller model $(P_1-P_0)Y$ and $(I-P_1)Y$ are $\sigma$ times projections
  of a standard Gaussian vector onto orthogonal subspaces, so TauCeti's
  projection laws and Fisher construction give the null statement by a
  short argument; the noncentral numerator law under the larger model
  follows as in 105.2.

### Quadratic forms and the analysis of variance

* **105.15. Distribution of quadratic forms.** Let $Y\sim N_n(\mu,\Sigma)$
  with $\Sigma$ positive definite, and let $A,B$ be symmetric. If $A\Sigma$
  is idempotent of rank $r$, then $Y^\top AY$ is noncentral chi-squared on
  $r$ degrees of freedom with noncentrality $\mu^\top A\mu$; for $\mu=0$,
  $Y^\top AY$ is chi-squared on $r$ degrees of freedom only if $A\Sigma$ is
  idempotent of rank $r$. If $A\Sigma B=0$, then $Y^\top AY$ and $Y^\top BY$
  are independent, and for $\mu=0$ this condition is also necessary
  (Craig–Sakamoto). For $\Sigma=I_n$ (Cochran's theorem): if
  $Y^\top Y=\sum_{i=1}^kY^\top A_iY$ with $\mathop{\mathrm{rank}}A_i=n_i$,
  the forms $Y^\top A_iY$ are independent noncentral chi-squared variables
  on $n_i$ degrees of freedom with noncentralities $\mu^\top A_i\mu$ if and
  only if $\sum_in_i=n$. TauCeti computes the domain and value of the
  moment-generating function of a centred Gaussian quadratic form and the
  chi-squared moment-generating function, proves the chi-squared laws and
  independence of squared Gaussian projections, the noncentral chi-squared
  law of $\|Y\|^2$ for identity covariance, and the criterion that linear
  images $AY$ and $BY$ of a Gaussian vector are independent if and only if
  $A\Sigma B^\top=0$. No law of a quadratic form $Y^\top AY$ is stated; the
  sufficiency of idempotence, its converse for $\mu=0$, the sufficiency
  half of Craig–Sakamoto, and Cochran's theorem follow from these results
  by short arguments. The necessity half of Craig–Sakamoto is missing.

* **105.16. Optimality of the $F$ test.** In the setting of 105.10, the
  power of the $F$ test of fixed level depends on the parameters only
  through $\delta^2=\|(P_1-P_0)X\beta\|^2/\sigma^2$ and is strictly
  increasing in $\delta^2$. Among level-$\alpha$ tests invariant under the
  group generated by positive rescaling of $Y$, translation within the
  smaller model space, and orthogonal transformations of the residual space
  and of the hypothesis space $\mathop{\mathrm{col}}(P_1-P_0)$, the $F$ test
  is uniformly most powerful. Among all similar tests of level $\alpha$, it
  maximizes the average power over every sphere of alternatives with fixed
  $\delta^2$, fixed nuisance mean component, and fixed $\sigma$. TauCeti
  defines the noncentral $F$ law, with its distribution function, and
  proves that the noncentral chi-squared law is stochastically nondecreasing
  in the noncentrality; the strict monotonicity of the power is not stated,
  and no theory of invariant or similar tests exists in any of the three
  libraries.

### Multivariate analysis, invariance, and graphical models

Let $G$ be an undirected graph on $\{1,\ldots,p\}$. A positive continuous
density on $\mathbb R^p$ has the **pairwise Markov property** if $X_i$ and
$X_j$ are conditionally independent given the other coordinates whenever
$\{i,j\}$ is not an edge; the **local Markov property** if each $X_i$ is
conditionally independent of the coordinates outside $\{i\}\cup\mathrm{ne}(i)$
given its neighbours $X_{\mathrm{ne}(i)}$; and the **global Markov property**
if $X_A$ and $X_B$ are conditionally independent given $X_S$ whenever $S$
separates $A$ from $B$ in $G$. It **factorizes** over $G$ if it is a product
of nonnegative functions $\psi_C(x_C)$ over the cliques $C$ of $G$.

* **105.22. Wishart distribution and Hotelling's $T^2$.** If $Z_1,\ldots,Z_n$
  are independent $N_p(0,\Sigma)$ with $n\ge p$ and $\Sigma$ positive
  definite, then $\sum_iZ_iZ_i^\top$ has the Wishart law $W_p(n,\Sigma)$ with
  its classical density. For an independent normal sample of size
  $n\ge p+1$, the sample mean $\bar X$ and the sample covariance $S$ with
  divisor $n-1$ are independent, $(n-1)S\sim W_p(n-1,\Sigma)$, and
  Hotelling's statistic $T^2=n(\bar X-\mu)^\top S^{-1}(\bar X-\mu)$
  satisfies
  $$\frac{n-p}{(n-1)p}\,T^2\sim F_{p,\,n-p}$$
  when the true mean is $\mu$. TauCeti proves the first sentence: its Gram
  law agrees with the density law and is almost surely positive definite.
  Not stated are the independence of $\bar X$ and $S$, the law of $(n-1)S$,
  and the law of $T^2$. They follow by a short argument: an orthogonal
  rotation of the sample separates $\bar X$ from $n-1$ independent
  $N_p(0,\Sigma)$ vectors whose Gram sum is $(n-1)S$, and the law of $T^2$
  follows from TauCeti's Schur-complement law for a block of size one,
  after a congruence, together with its Fisher construction.

* **105.23. Wilks's lambda.** In the multivariate normal linear model
  $Y=XB+U$, with $Y$ of size $n\times p$, $X$ a fixed $n\times q$ matrix of
  rank $q$, and the rows of $U$ independent $N_p(0,\Sigma)$ with $\Sigma$
  positive definite, consider a hypothesis $CB=0$ with $C$ of size
  $h\times q$ and rank $h$. Let $E=Y^\top(I-P_X)Y$, let $H=E_0-E$ with $E_0$
  the residual matrix under the hypothesis, write $e=n-q\ge p$ and
  $\Lambda=\det(E)/\det(E+H)$. Under the hypothesis, $E\sim W_p(e,\Sigma)$
  and $H\sim W_p(h,\Sigma)$ are independent, and $\Lambda$ has the law of a
  product of independent $V_i\sim\mathrm{Beta}((e+1-i)/2,h/2)$,
  $i=1,\ldots,p$. With $k=e-(p-h+1)/2$, for fixed $z$, $p$, $h$,
  $$P(-k\log\Lambda\le z)=P(\chi^2_{ph}\le z)+O(e^{-2})
  \qquad(e\to\infty).$$
  TauCeti proves the univariate Gamma–Beta relation; the matrix-variate
  Beta law, the product representation, and the expansion are absent.

* **105.24. Principal component eigenvalues.** Let $S_n$ be the sample
  covariance, with divisor $n$, of an independent normal sample in
  $\mathbb R^p$, and let $\lambda_j$ be a simple positive eigenvalue of the
  population covariance. The corresponding eigenvalue $\hat\lambda_j$ of
  $S_n$ satisfies $\sqrt n\,(\hat\lambda_j-\lambda_j)\Rightarrow
  N(0,2\lambda_j^2)$. None of the three libraries states eigenvalue
  asymptotics for sample covariances.

* **105.26. Undirected graphical models.** For a positive continuous
  density, the pairwise, local, and global Markov properties are
  equivalent. A density that factorizes over $G$ is globally Markov;
  conversely (Hammersley–Clifford), a positive continuous density with the
  pairwise Markov property factorizes over $G$ with positive factors. For
  a nondegenerate Gaussian law, $X_i$ and $X_j$ are conditionally
  independent given the remaining coordinates if and only if the $(i,j)$
  entry of the precision matrix vanishes. Mathlib defines conditional
  independence and TauCeti proves weak union and related rules, but no
  Markov property relative to a graph is defined and the intersection
  property for positive densities is absent. The Gaussian criterion is
  close to TauCeti's Gaussian conditioning theorem and its criterion for
  independence of complementary Gaussian blocks, since the conditional
  covariance of a pair given the rest is the inverse of the corresponding
  $2\times2$ block of the precision matrix.

### Covariance geometry and multivariate reduction

* **105.28. Gaussian covariance likelihood.** For a normal sample with
  unknown mean and positive definite covariance, if the centred sample
  spans $\mathbb R^p$, the maximum likelihood estimators are $\hat\mu=\bar X$
  and $\hat\Sigma=n^{-1}\sum_i(X_i-\bar X)(X_i-\bar X)^\top$. If that scatter
  matrix is singular, the likelihood is unbounded over positive definite
  covariances and has no maximizer there; this occurs almost surely when
  $n\le p$. TauCeti proves the classical density of a nondegenerate
  multivariate Gaussian, which is the likelihood; its maximization is not
  stated.

* **105.29. Canonical correlations.** For centred random vectors $(U,V)$ with
  positive definite marginal covariances, the largest correlation between
  $a^\top U$ and $b^\top V$ is the largest singular value of
  $\Sigma_{UU}^{-1/2}\Sigma_{UV}\Sigma_{VV}^{-1/2}$. Subsequent singular
  values solve the same maximization with successive variates uncorrelated
  within each vector; they lie in $[0,1]$ and are unchanged by nonsingular
  linear transformations within $U$ or $V$. For a jointly Gaussian pair,
  all canonical correlations vanish if and only if $U$ and $V$ are
  independent. TauCeti proves the Gaussian independence criterion in
  cross-covariance form and defines principal cosines between subspaces;
  the variational characterization and the invariance are missing.

### Wishart structure and correlation coefficients

* **105.31. Structure of the Wishart law.** Let $W\sim W_p(n,\Sigma)$ with
  $n\ge p$ an integer and $\Sigma$ positive definite. Then $W$ has density
  $$\frac{(\det w)^{(n-p-1)/2}\exp\bigl(-\tfrac12\mathop{\mathrm{tr}}(\Sigma^{-1}w)\bigr)}
  {2^{np/2}(\det\Sigma)^{n/2}\,\Gamma_p(n/2)}$$
  on positive definite matrices, and $MWM^\top\sim W_k(n,M\Sigma M^\top)$ for
  a $k\times p$ matrix $M$ of rank $k$. With blocks of sizes $k$ and $p-k$,
  $W_{22}\sim W_{p-k}(n,\Sigma_{22})$, and the Schur complement
  $W_{11\cdot2}=W_{11}-W_{12}W_{22}^{-1}W_{21}$ is $W_k(n-p+k,\Sigma_{11\cdot2})$
  and independent of $(W_{12},W_{22})$. If $\Sigma=I_p$ and $W=T^\top T$ with
  $T$ upper triangular with positive diagonal, the entries $t_{ij}$,
  $i\le j$, are independent, with $t_{ii}^2\sim\chi^2_{n-i+1}$ and
  $t_{ij}\sim N(0,1)$ for $i<j$ (Bartlett). Consequently $\det W/\det\Sigma$
  has the law of a product of independent $\chi^2_{n-i+1}$ variables. TauCeti
  proves the density, the congruence and marginal statements, the Bartlett
  decomposition, and the determinant law (for real degree), and the
  Schur-complement law for a block of size one, $k=1$, in the form that
  $1/(W^{-1})_{ii}$ is $1/(\Sigma^{-1})_{ii}$ times a $\chi^2_{n-p+1}$
  variable. Missing are the Schur-complement law for general $k$ and its
  independence of $(W_{12},W_{22})$, which would combine Gaussian
  conditioning with the Gram representation.

* **105.32. Sampling theory of correlation coefficients.** Let $r$ be the
  sample correlation of $N$ independent observations from a bivariate
  normal law with correlation $\rho$. If $\rho=0$ and $N>2$, then
  $\sqrt{N-2}\,r/\sqrt{1-r^2}$ has law $t_{N-2}$. As $N\to\infty$,
  $\sqrt N(r-\rho)\Rightarrow N(0,(1-\rho^2)^2)$ and
  $\sqrt N(\mathop{\mathrm{artanh}}r-\mathop{\mathrm{artanh}}\rho)\Rightarrow
  N(0,1)$. For a $p$-variate normal sample, the sample partial correlation
  of two coordinates given $p-q$ others has the law of an ordinary sample
  correlation from $N-(p-q)$ observations with $\rho$ replaced by the
  population partial correlation. If the population multiple correlation of
  $X_1$ with $(X_2,\ldots,X_p)$ vanishes and $N>p$, the sample multiple
  correlation satisfies
  $$\frac{R^2}{1-R^2}\cdot\frac{N-p}{p-1}\sim F_{p-1,\,N-p}.$$
  TauCeti's Student and Fisher constructions are the final steps, and
  Mathlib has $\mathop{\mathrm{artanh}}$ and the continuous-mapping and
  Slutsky theorems; no sample correlation is defined.

### Tests on covariance structure and multivariate hypotheses

Here $X_1,\ldots,X_N$ are independent $N_p(\mu,\Sigma)$ with $N>p$, $n=N-1$,
and $A=\sum_i(X_i-\bar X)(X_i-\bar X)^\top$.

* **105.33. Likelihood-ratio tests of sphericity and independence.** For
  $H:\Sigma=\lambda I_p$ with $\lambda>0$ unspecified, the likelihood ratio is
  $V^{N/2}$ with $V=\det A/(\mathop{\mathrm{tr}}A/p)^p$. Under $H$,
  $-N\log V\Rightarrow\chi^2_f$ with $f=p(p+1)/2-1$, and with
  $\rho=1-(2p^2+p+2)/(6pn)$ the distribution function of $-n\rho\log V$
  differs from that of $\chi^2_f$ by $O(n^{-2})$. For independence of $k$
  subvectors of sizes $p_1,\ldots,p_k$, the likelihood ratio is
  $\Lambda^{N/2}$ with $\Lambda=\det A/\prod_i\det A_{ii}$; under
  independence $-N\log\Lambda\Rightarrow\chi^2_f$ with $f=\sum_{i<j}p_ip_j$,
  and with Box's multiplier
  $$m=N-\frac32-\frac{p^3-\sum_ip_i^3}{3\bigl(p^2-\sum_ip_i^2\bigr)}$$
  the distribution function of $-m\log\Lambda$ differs from that of
  $\chi^2_f$ by $O(N^{-2})$ for fixed $p_1,\ldots,p_k$. For $k=2$,
  $\Lambda=\prod_i(1-r_i^2)$ with $r_i$ the sample canonical correlations.
  TauCeti's Wishart characteristic function and trace moment-generating
  functions are supporting material; no test statistic is formulated.

* **105.34. Invariant tests of a multivariate linear hypothesis.** In the
  setting of 105.23 let $E$ be positive definite and let
  $l_1\ge\cdots\ge l_p\ge0$ be the roots of $\det(H-lE)=0$. Under the group
  of nonsingular linear maps of the response, together with the translations
  and orthogonal maps that leave the problem invariant, these roots form a
  maximal invariant, so every invariant test is a function of them. Wilks's
  statistic is $\prod_i(1+l_i)^{-1}$, the Lawley–Hotelling trace is
  $\sum_il_i$, the Pillai trace is $\sum_il_i/(1+l_i)$, and Roy's statistic
  is $l_1$. Under the null hypothesis
  $e\mathop{\mathrm{tr}}HE^{-1}\Rightarrow\chi^2_{ph}$ as $e\to\infty$. If
  $\min(p,h)=1$, all four tests reduce to the same exact $F$ test. None of
  the three libraries has a theory of invariant tests or these statistics.

* **105.35. Factor analysis and identification.** In the orthogonal factor
  model $X=\mu+\Lambda f+u$, with $p\times m$ loadings $\Lambda$,
  $\mathbb Ef=0$, $\mathop{\mathrm{Cov}}f=I_m$, and $u$ of mean $0$,
  uncorrelated with $f$, with diagonal positive definite covariance $\Psi$, the loadings $\Lambda O$ give the
  same covariance for every orthogonal $O$, and a normalized $\Lambda$ (with
  $\Lambda^\top\Psi^{-1}\Lambda$ diagonal with distinct decreasing entries)
  is unique up to column signs given $\Lambda\Lambda^\top$ and $\Psi$.
  Suppose $\Sigma=\Lambda_0\Lambda_0^\top+\Psi_0$ is attained by a unique pair
  $(\Lambda_0\Lambda_0^\top,\Psi_0)$, with $\Lambda_0$ normalized, and let $C$
  be the sample covariance. If $C\to_P\Sigma$, the Gaussian maximum likelihood
  estimators $\hat\Psi$ and $\hat\Lambda$, with suitable column signs, are
  consistent. With
  $(\theta_{ij})=\Psi_0-\Lambda_0(\Lambda_0^\top\Psi_0^{-1}\Lambda_0)^{-1}\Lambda_0^\top$
  and $\Lambda_0$ of rank $m$, if $\sqrt n(C-\Sigma)$ has a normal limit and
  $(\theta_{ij}^2)$ is nonsingular, then $\sqrt n(\hat\Lambda-\Lambda_0)$ and
  $\sqrt n(\hat\Psi-\Psi_0)$ have normal limits (Anderson and Rubin). For a
  Gaussian sample, $-2$ times the log likelihood ratio against an
  unrestricted covariance converges to chi-squared on
  $\frac12[(p-m)^2-p-m]$ degrees of freedom when this number is positive.
  None of the three libraries treats factor models.

### Decomposable graphical models

A graph is **decomposable** when every cycle of length at least four has a
chord; its cliques $\mathcal C$ then admit a perfect order with complete
separators $\mathcal S$, of multiplicities $\nu(S)$ independent of the order.
For a matrix $B$ indexed by $C$, $[B]^V$ is the $p\times p$ matrix with $B$ in
the block $C\times C$ and zeros elsewhere.

* **105.36. Decomposable models.** For a decomposable graph, a positive
  density is globally Markov if and only if
  $$f(x)=\frac{\prod_{C\in\mathcal C}f_C(x_C)}
  {\prod_{S\in\mathcal S}f_S(x_S)^{\nu(S)}},$$
  with $f_C,f_S$ the marginal densities. In the Gaussian model whose
  concentration matrix vanishes off the edges, with $\mathrm{ssd}$ the
  centred sum-of-squares matrix of $n$ observations, the maximum likelihood
  estimator exists with probability one if and only if $n>\max_C|C|$, and
  then
  $$\hat K=n\Bigl(\sum_{C\in\mathcal C}\bigl[(\mathrm{ssd}_C)^{-1}\bigr]^V
  -\sum_{S\in\mathcal S}\nu(S)\bigl[(\mathrm{ssd}_S)^{-1}\bigr]^V\Bigr).$$
  For a general graph the estimate, when it exists, is the unique positive
  definite $\hat\Sigma$ that matches $\mathrm{ssd}/n$ on the diagonal and the
  edges and whose inverse vanishes off the edges; it exists whenever
  $\mathrm{ssd}$ is positive definite, in particular almost surely when
  $n>p$, and iterative proportional scaling converges to it. TauCeti has two-marginal iterative proportional fitting
  for measures; chordal graphs, separators, and the Gaussian clique scaling
  are absent.

### Experimental design

For a regression function $f(x)\in\mathbb R^p$, continuous on a compact design
space, and a design measure $\xi$, the information matrix is
$M(\xi)=\int f(x)f(x)^\top\,\xi(dx)$.

* **105.37. Kiefer–Wolfowitz equivalence.** Assume $M(\xi^*)$ is
  nonsingular. Then $\xi^*$ maximizes $\det M(\xi)$ if and only if
  $\max_xf(x)^\top M(\xi^*)^{-1}f(x)=p$, with equality on the support of
  $\xi^*$. For a criterion that is concave and strictly increasing in the
  Loewner order and differentiable at $M(\xi^*)$, the design $\xi^*$ is
  optimal if and only if the directional derivative of the criterion at
  $M(\xi^*)$ is nonpositive in the direction of every one-point design.
  TauCeti proves concavity of $(\det A)^{1/n}$ on positive semidefinite
  matrices; the information matrix of a design and the equivalence theorem
  are absent.

* **105.38. Randomization test.** Under the sharp null hypothesis that each
  unit's response is unchanged by its treatment assignment, redraw the
  assignment from the randomization distribution while holding the
  responses fixed. The induced law of a test statistic is free of unknown
  parameters, and the test that rejects when the observed statistic lies in
  the upper fraction $\alpha$ of this law has conditional level at most
  $\alpha$ given the responses, hence unconditional level at most $\alpha$;
  the conditional level equals $\alpha$ when the randomization law is
  atomless or ties are broken by auxiliary randomization. Mathlib has the
  uniform probability on a finite set, but no randomization test is
  formulated. The statement follows by a short argument: given the
  responses, the observed statistic is a draw from the randomization law,
  so the rejection probability is at most $\alpha$ by the definition of the
  upper $\alpha$ fraction, and integration over the responses gives the
  unconditional bound.

### Optimality of block and polynomial designs

For a block design with incidence matrix $N$, diagonal replication matrix $R$,
and diagonal block-size matrix $K$, the information matrix is
$C_d=R-NK^{-1}N^\top$. For a connected design with positive eigenvalues
$\mu_1,\ldots,\mu_{v-1}$ of $C_d$, the design is **A-**, **D-**, or
**E-optimal** in a class if it minimizes $\sum_i\mu_i^{-1}$, maximizes
$\prod_i\mu_i$, or maximizes $\min_i\mu_i$, respectively.

* **105.42. Fisher's inequality and optimality of balanced incomplete
  blocks.** A balanced incomplete block design with $v$ treatments and $b$
  blocks satisfies $b\ge v$. Every block design with $b$ blocks of size
  $k<v$ has $\mathop{\mathrm{tr}}C_d\le b(k-1)$, with equality exactly when
  no treatment occurs twice in a block. A balanced incomplete block design
  attains this bound and has all $v-1$ positive eigenvalues equal to
  $\lambda v/k=b(k-1)/(v-1)$; hence, if one exists, it is A-, D-, and
  E-optimal among block designs with the same $v$, $b$, $k$, and more
  generally it minimizes every criterion of $C_d$ that is convex, invariant
  under relabeling of treatments, and nonincreasing under multiplication of
  $C_d$ by scalars at least $1$ (Kiefer's universal optimality). Mathlib's
  theorem that a nondegenerate configuration in which every two points lie
  on a line has at least as many lines as points gives Fisher's inequality
  in the case $\lambda=1$. The case $\lambda\ge2$ and all optimality
  statements are missing.

### Latin squares and regular fractions

A **Latin square** of order $n$ is an $n\times n$ array of $n$ symbols, each
occurring once in every row and column; two are **orthogonal** when,
superimposed, every ordered pair of symbols occurs in exactly one cell. An
$N\times k$ array on $s$ symbols is an **orthogonal array of strength $t$**
when every $t$-tuple appears equally often in every set of $t$ columns.

* **105.44. Latin squares and mutually orthogonal sets.** In the additive
  model with row, column, and treatment effects for a Latin square of order
  $n\ge3$, with independent homoscedastic errors, the spaces of row,
  column, and treatment contrasts are mutually orthogonal; the corrected
  total sum of squares splits into rows, columns, treatments, and residual
  with $n-1$, $n-1$, $n-1$, and $(n-1)(n-2)$ degrees of freedom; and the
  least-squares estimator of a difference of two treatment effects is the
  difference of the treatment means, with variance $2\sigma^2/n$. A set of
  $k$ mutually orthogonal Latin squares of order $s$ is equivalent to an
  orthogonal array with $s^2$ rows and $k+2$ columns on $s$ symbols of
  strength $2$; consequently $k\le s-1$, and the bound is attained when $s$
  is a prime power. Mathlib has Galois fields of every prime-power order and
  finite projective planes, from which the classical construction proceeds;
  Latin squares, orthogonal arrays, the bound, and the construction are
  absent.

### Survey sampling and finite populations

A **sampling design** is a probability law on the subsets $s$ of a finite
population $U=\{1,\ldots,N\}$. The values $y_i\in\mathbb R$ are fixed;
only $s$ is random. Put $I_i=1_{\{i\in s\}}$,
$\pi_i=\mathbb E I_i$, $\pi_{ij}=\mathbb E I_iI_j$, with
$\pi_{ii}=\pi_i$, and $\Delta_{ij}=\pi_{ij}-\pi_i\pi_j$.

* **105.72. Horvitz–Thompson estimation and design variance.** Assume
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

* **105.73. Simple and stratified random sampling; Neyman allocation.**
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

The libraries supply finite probability laws, indicator expectations,
covariance expansions, and TauCeti's sampling without replacement, but none
of the three states these sampling formulas. Short
derivations are given in [GAPS_EASY.md](GAPS_EASY.md).

### Experiments, identification, and estimation

A unit has **potential outcomes** $Y(a)$ for each treatment level $a$; under
the stable unit treatment value assumption the observed outcome is the
potential outcome of the treatment received. For binary $A$ the **average
treatment effect** is $\theta=\mathbb E[Y(1)-Y(0)]$. Write
$e_a(x)=P(A=a\mid X=x)$, $m_a(x)=\mathbb E[Y\mid A=a,X=x]$, and $e=e_1$ for the
**propensity score**. **Conditional ignorability** is $Y(a)\perp A\mid X$,
and **positivity** at level $a$ is $e_a(X)\ge\delta>0$ almost surely. A
measurable $b(X)$ is a **balancing score** when $A\perp X\mid b(X)$.

In a completely randomized experiment on $n$ units, a simple random subset
of $n_1$ units is treated and the other $n_0=n-n_1$ are controls; the
potential outcomes are fixed. Write $\tau_i=Y_i(1)-Y_i(0)$, $\tau$ for their
average, $S^2(a)$ and $S^2(\tau)$ for the finite-population variances (divisor
$n-1$) of the $Y_i(a)$ and $\tau_i$, $\hat\tau$ for the difference of the arm
means, and $\hat S^2(a)$ for the sample variance in arm $a$ (divisor $n_a-1$).

* **105.46. Neyman's theorem.** In a completely randomized experiment,
  $\mathbb E\hat\tau=\tau$ and
  $$\mathop{\mathrm{Var}}(\hat\tau)
  =\frac{S^2(1)}{n_1}+\frac{S^2(0)}{n_0}-\frac{S^2(\tau)}{n}.$$
  The estimator $\hat V=\hat S^2(1)/n_1+\hat S^2(0)/n_0$ satisfies
  $\mathbb E\hat V-\mathop{\mathrm{Var}}(\hat\tau)=S^2(\tau)/n\ge0$, with
  equality if and only if all $\tau_i$ are equal. TauCeti defines sampling
  without replacement as reading the population along a uniform injective
  selection, and Statlib's potential-response notation expresses the
  observed outcomes $Y_i(A_i)$; no assignment mechanism or design-based
  estimator is defined. The theorem is a finite computation from the
  covariances of the treatment indicators under that law, which are not
  stated.

* **105.47. Identification by regression and by weighting.** Under
  conditional ignorability and positivity at level $a$, and if
  $\mathbb E|Y(a)|<\infty$,
  $$\mathbb E[Y(a)]=\mathbb E[m_a(X)]
  =\mathbb E\Bigl[\frac{1_{\{A=a\}}Y}{e_a(X)}\Bigr],$$
  so for binary treatment $\theta=\mathbb E[m_1(X)-m_0(X)]$ when the
  hypotheses hold at both levels. Statlib's potential-response notation
  gives $Y(a)$ and the observed outcome under consistency, but no
  potential-outcome model with a probability structure is defined in any
  of the three libraries. The identities follow by a short argument from Mathlib's conditional
  independence and conditional expectation: by ignorability
  $\mathbb E[Y(a)\mid X]=\mathbb E[Y(a)\mid A=a,X]=m_a(X)$, and the tower
  property gives both expressions.

* **105.48. Propensity score.** Under conditional ignorability, $Y(a)$ is
  conditionally independent of $A$ given $e(X)$. The propensity score is a
  balancing score, and it is a function of every balancing score. This
  follows by a short argument from Mathlib's conditional expectation, since
  $P(A=1\mid Y(a),e(X))$ and $P(A=1\mid X,e(X))$ both reduce to $e(X)$ by
  the tower property; it is not stated in any of the three libraries.

Let $\mu_a$ be candidate regressions and $e$ a candidate propensity score,
let $e_0$ be the true propensity score, and set
$$\varphi=\mu_1(X)-\mu_0(X)+\frac{A(Y-\mu_1(X))}{e(X)}
-\frac{(1-A)(Y-\mu_0(X))}{1-e(X)}.$$

* **105.49. Doubly robust estimator of the average treatment effect.**
  Assume conditional ignorability and $e_0(X)\in[\delta,1-\delta]$. Then
  $\mathbb E\varphi=\theta$ as soon as either $e=e_0$ and the $\mu_a$ are
  square-integrable, or $\mu_a=m_a$ for both $a$ and $e$ is measurable with
  values in $[\delta,1-\delta]$. Let $\hat\theta$ be the cross-fitted average
  of $\varphi$ (SYNOPSIS102, item 39), with fitted $\hat e$ in
  $[\delta,1-\delta]$, and suppose $\mathbb EY^2<\infty$. If
  $\|\hat\mu_a-m_a\|_2\to_P0$, $\|\hat e-e_0\|_2\to_P0$,
  $\|\hat\mu_a-m_a\|_2\|\hat e-e_0\|_2=o_P(n^{-1/2})$ for both $a$, and the
  fitted $\varphi$ converge in $L^2$ to the true one, then
  $$\sqrt n(\hat\theta-\theta)=n^{-1/2}\sum_{i=1}^n
  \bigl(\varphi_0(O_i)-\theta\bigr)+o_P(1),$$
  with $\varphi_0$ the function $\varphi$ at the true nuisances and $O_i$
  the observations. None of the three libraries has a potential-outcome
  model beyond Statlib's notation, cross-fitting, or the semiparametric
  theory of SYNOPSIS102 on which the expansion rests.

Let $Z\in\{0,1\}$ be an instrument with potential treatments $A(z)$ and
potential outcomes $Y(z,a)$; **exclusion** means $Y(0,a)=Y(1,a)=Y(a)$, and
**monotonicity** means $A(1)\ge A(0)$ almost surely.

* **105.50. Local average treatment effect.** If
  $(Y(0),Y(1),A(0),A(1))$ is independent of $Z$, exclusion and monotonicity
  hold, and $P(A=1\mid Z=1)\ne P(A=1\mid Z=0)$, then
  $$\frac{\mathbb E[Y\mid Z=1]-\mathbb E[Y\mid Z=0]}
  {\mathbb E[A\mid Z=1]-\mathbb E[A\mid Z=0]}
  =\mathbb E\bigl[Y(1)-Y(0)\mid A(1)>A(0)\bigr].$$
  Not stated in any of the three libraries. It follows by a short
  computation from independence:
  the numerator equals $\mathbb E[(Y(1)-Y(0))(A(1)-A(0))]$, and
  monotonicity makes $A(1)-A(0)$ the complier indicator.

### Treated-unit effects and instrumental variables

In the linear instrumental-variable model $Y=D^\top\beta+\varepsilon$, the
instrument vector $Z$ satisfies $\mathbb E[Z\varepsilon]=0$, with
$\mathbb E[ZZ^\top]$ nonsingular and $\mathbb E[ZD^\top]$ of full column rank;
observed and exogenous regressors are included in both $D$ and $Z$.
Two-stage least squares regresses $D$ on $Z$ and then $Y$ on the fitted
values $\hat D$.

* **105.55. Two-stage least squares.** For independent copies with finite
  second moments, $\hat\beta_{\mathrm{tsls}}\to_P\beta$. With
  $Q_{ZZ}=\mathbb E[ZZ^\top]$, $Q_{ZD}=\mathbb E[ZD^\top]$,
  $H=Q_{ZD}^\top Q_{ZZ}^{-1}Q_{ZD}$, and $\Omega=\mathbb E[\varepsilon^2ZZ^\top]$,
  if $\Omega$ is finite, then
  $$\sqrt n(\hat\beta_{\mathrm{tsls}}-\beta)\Rightarrow N\bigl(0,\;
  H^{-1}Q_{ZD}^\top Q_{ZZ}^{-1}\,\Omega\,Q_{ZZ}^{-1}Q_{ZD}H^{-1}\bigr),$$
  and if moreover $Z$ and $D$ have finite fourth moments, the covariance is
  estimated consistently with sample moments and residuals. When $D$ and
  $Z$ have the same dimension it is the
  instrumental-variable estimator; for binary $Z$ and $D$ without
  covariates it is the sample Wald ratio, whose limit under the assumptions
  of 105.50 is the complier effect. Mathlib's strong law, scalar central
  limit theorem, Cramér–Wold device, and Slutsky's theorem are the
  ingredients; the estimator and its asymptotics are not formulated.

### Efficiency, partial identification, and design-based identification

* **105.56. Efficient variance for an average treatment effect.** Under the
  assumptions of 105.49, with $\sigma_a^2(X)=\mathop{\mathrm{Var}}(Y\mid A=a,X)$
  and the following expression finite, the efficient influence function in
  the unrestricted observed-data model is $\varphi-\theta$ at the true
  nuisances, with variance
  $$\mathop{\mathrm{Var}}(m_1(X)-m_0(X))+
  \mathbb E\left[\frac{\sigma_1^2(X)}{e_0(X)}+
  \frac{\sigma_0^2(X)}{1-e_0(X)}\right],$$
  and the cross-fitted estimator of 105.49 is asymptotically normal with
  this variance. Efficient influence functions are absent from all three
  libraries.

### Graphical interventions

Let $G$ be a directed acyclic graph on a finite vertex set $V$, and let
$\xi=(\xi_v)$ have a density $p$ with respect to a product measure. The law
**factorizes recursively** when $p(x)=\prod_vp(x_v\mid x_{\mathrm{pa}(v)})$;
it is **local directed Markov** when each $\xi_v$ is conditionally
independent of its nondescendants given its parents. A path is **blocked** by
$W$ when some noncollider on it lies in $W$ or some collider has no
descendant, itself included, in $W$; disjoint sets are **$d$-separated** by a
third when every path between them is blocked, and the **global Markov
property** says that $d$-separation implies conditional independence. For
discrete variables, $\mathop{\mathrm{do}}(X=x)$ is the truncated factorization
$P(v\mid\mathop{\mathrm{do}}(x))=\prod_{u\notin X}P(v_u\mid v_{\mathrm{pa}(u)})$ on
configurations consistent with $x$. $G_{\bar X}$ removes the arrows into $X$
and $G_{\underline Z}$ the arrows out of $Z$. A **back-door path** from $X$
starts with an arrow into $X$. $Z$ satisfies the **back-door criterion** for
$(X,Y)$ when it contains no descendant of $X$ and blocks every back-door path
from $X$ to $Y$; it satisfies the **front-door criterion** when it intercepts
every directed path from $X$ to $Y$, every back-door path from $X$ to $Z$ is
blocked, and $X$ blocks every back-door path from $Z$ to $Y$. Conditioning
events are assumed to have positive probability.

* **105.62. Directed Markov properties.** For a law with a density as above,
  recursive factorization along $G$, the local directed Markov property,
  and the global Markov property are equivalent. Mathlib has directed
  graphs as relations and kernel composition, and TauCeti has semigraphoid
  rules for conditional independence; directed acyclic graphs,
  $d$-separation, and directed Markov properties are not defined.

* **105.63. Back-door and front-door formulae.** For discrete variables
  factorizing recursively along $G$: if $Z$ satisfies the back-door
  criterion relative to $(X,Y)$, then
  $P(y\mid\mathop{\mathrm{do}}(x))=\sum_zP(y\mid x,z)P(z)$; if $Z$ satisfies
  the front-door criterion, then
  $$P\bigl(y\mid\mathop{\mathrm{do}}(x)\bigr)
  =\sum_z P(z\mid x)\sum_{x'}P(y\mid x',z)\,P(x').$$
  Not stated in any of the three libraries.

* **105.64. Rules of the do-calculus.** For disjoint vertex sets $X,Y,Z,W$,
  with $Z(W)$ the vertices of $Z$ that are not ancestors of $W$ in
  $G_{\bar X}$,
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
  &&\text{if }(Y\perp Z\mid X,W)_{G_{\bar X,\overline{Z(W)}}},
  \end{aligned}
  $$
  the conditions being $d$-separation in the indicated graphs. With some
  vertices unobserved, call $P(y\mid\mathop{\mathrm{do}}(x))$ identifiable
  when it agrees for any two laws factorizing along $G$ with the same
  positive observed marginal. It is identifiable if and only if finitely
  many applications of the three rules and the ordinary rules of
  probability reduce it to an expression in the observed law. The same
  holds for conditional queries $P(y\mid\mathop{\mathrm{do}}(x),z)$, with $Z$
  a further disjoint set of observed vertices, when $G$ is semi-Markovian
  (every unobserved vertex is a root with exactly two children, both
  observed) and identifiability is required over all laws
  factorizing along $G$ with $P(z\mid\mathop{\mathrm{do}}(x))>0$. Absent from
  all three libraries.

* **105.65. Longitudinal $g$-formula.** Let treatments $A_0,\ldots,A_T$
  follow covariates $L_t$ measured before $A_t$, with $L_0$ baseline and
  histories $H_t=(L_0,A_0,\ldots,A_{t-1},L_t)$, and let $Y(\bar a)$ be the
  outcome under the regime $\bar a=(a_0,\ldots,a_T)$. Assume consistency,
  sequential exchangeability
  $Y(\bar a)\perp A_t\mid H_t,A_{0:t-1}=a_{0:t-1}$ at each $t$, and
  sequential positivity (a lower bound, uniform in $t$, on the conditional
  probability of $A_t=a_t$ given the observed past). Then, for discrete
  covariates,
  $$\mathbb E[Y(\bar a)]
  =\sum_{\bar l}\mathbb E[Y\mid\bar L_T=\bar l,\bar A_T=\bar a]
  P(L_0=l_0)\prod_{t=1}^T
  P(L_t=l_t\mid\bar L_{t-1}=\bar l_{t-1},\bar A_{t-1}=\bar a_{t-1}),$$
  with integrals against the conditional kernels in general; equivalently
  $\mathbb E[Y(\bar a)]=\mathbb E[Q_0]$ for the iterated conditional
  expectations $Q_{T+1}=Y$,
  $Q_t=\mathbb E[Q_{t+1}\mid\bar L_t,\bar A_t=\bar a_t]$. Mathlib's kernel
  composition and Ionescu–Tulcea construction give the measure-theoretic
  form of the iterated integral; the causal statement is not formulated.

* **105.67. Markov equivalence of directed graphs.** Two directed acyclic
  graphs have the same $d$-separation relations if and only if they have
  the same skeleton and the same unshielded colliders $i\to j\leftarrow k$
  with $i,k$ nonadjacent. If a law is faithful to $G$, that is, its
  conditional independences are exactly those implied by $d$-separation in
  $G$, then the directed acyclic graphs to which it is faithful are exactly
  those Markov equivalent to $G$. Absent from all three libraries.

### Causal discovery

* **105.70. Skeleton and colliders from conditional independences.** In a
  directed acyclic graph, two vertices are adjacent if and only if no
  subset of the other vertices $d$-separates them, and two nonadjacent
  vertices are $d$-separated by the parents of one of them. If $i-j-k$ is a
  skeleton path with $i,k$ nonadjacent and $S$ $d$-separates $i$ and $k$,
  then $i\to j\leftarrow k$ if and only if $j\notin S$. Consequently, for a
  law that is globally Markov and faithful to $G$, the conditional
  independences determine the skeleton, the unshielded colliders, and hence
  the Markov equivalence class, and the PC algorithm with exact
  conditional-independence answers returns the skeleton and the unshielded
  colliders. Absent from all three libraries.

* **105.71. Identifiability of restricted structural equation models.**
  Suppose $X_j=\sum_{k\in\mathrm{pa}(j)}\beta_{jk}X_k+N_j$ along a directed
  acyclic graph $G$, with jointly independent noises and $\beta_{jk}\ne0$ on
  every edge. If the noises are non-Gaussian with strictly positive
  densities, or Gaussian with a common variance, then $G$ is identifiable
  from the joint law. The same holds for $X_j=f_j(X_{\mathrm{pa}(j)})+N_j$
  with Gaussian noises and three times differentiable $f_j$ nonlinear in
  each argument. Among linear Gaussian representations with unrestricted
  positive noise variances that are faithful to their respective graphs,
  two graphs carry the same joint law exactly when they are Markov equivalent.
  Nonzero edge coefficients alone do not imply faithfulness. Absent from all three
  libraries.

## 106. Dependent data and stochastic models

None of the three libraries defines a weakly stationary process, an
autocovariance or spectral density of a process, an ARMA or GARCH model, a
point process in space, a counting-process martingale, a sequential test, or
a domain of attraction. Mathlib supplies the independent-data limit theory
(the central limit theorem for independent identically distributed real
summands, Lévy's continuity theorem, the Cramér–Wold device, Slutsky's
theorem, and the binomial-to-Poisson limit), discrete-time martingales with
Doob's maximal inequality and optional stopping at bounded stopping times,
orthogonal projection and Gram–Schmidt orthogonalization, von Neumann's mean
ergodic theorem and the maximal ergodic theorem, the projective limit of
finite-dimensional laws on products of Polish spaces, Fourier series on the
circle, and the exponential, Pareto and Poisson laws. TauCeti adds Herglotz's
theorem on $\mathbb Z$ and Bochner's theorem on $\mathbb R^d$, Gaussian
conditioning with positive-semidefinite covariance (which is the one-step
Kalman update and the Gaussian kriging formula), the path law of a Markov
chain with recurrence, periods, return gaps, the strong Markov property and
the coupling inequality, the $L^2$ ergodic theorem towards the conditional
expectation on the invariant $\sigma$-algebra, renewal theory (the strong
law and the elementary renewal theorem for the renewal count, its central
limit theorem, and the Poisson counts of the exponential renewal process),
Doob's maximal inequality in general time, the hazard representation of a
survival function and the additivity of hazards under independent minima,
laws of minima and maxima of independent families, the Gumbel and Weibull
laws, the generalized extreme-value and generalized Pareto families with
their max- and threshold-stability, and order statistics. Statlib adds the
sequential-sampling layer: Wald's identity for integrable stopping times of
independent identically distributed sequences, the likelihood ratio and the
Kullback–Leibler divergence of laws stopped at such a time, and e-variables
with their products and the numeraire. The
principal omissions are central limit theorems for dependent data and the
asymptotics of time-series estimators built on them, the spectral theory of
stationary processes, equivalence of Gaussian measures in prediction,
counting-process martingales and the survival estimators they support,
sequential testing with unbounded stopping times, optimal change detection,
and the extreme-value limit theory based on regular variation. Ville's
inequality and the forward direction of the Poisson approximation for
exceedances are selected although each follows from library results by a
short argument, which is indicated.

Sources: [mathematical synopsis](SYNOPSIS106.md); [combined coverage inventory](STRUCTURE106.md).

Unless stated otherwise, $(X_t)_{t\in\mathbb Z}$ is a real, weakly stationary,
mean-zero process with $\mathbb EX_t^2<\infty$ and autocovariance
$\gamma(h)=\mathop{\mathrm{Cov}}(X_{t+h},X_t)$, $\rho(h)=\gamma(h)/\gamma(0)$,
and $\bar X_n$ is the mean of $X_1,\ldots,X_n$. Write $P_{t-1}$ for orthogonal
projection in $L^2$ onto the closed linear span of $\{X_s:s\le t-1\}$. The
spectral density is
$f(\omega)=(2\pi)^{-1}\sum_h\gamma(h)e^{-ih\omega}$ on $[-\pi,\pi]$ and the
periodogram is $I_n(\omega)=(2\pi n)^{-1}|\sum_{t=1}^nX_te^{-it\omega}|^2$. The
sample autocovariances are
$\hat\gamma(h)=n^{-1}\sum_{t=1}^{n-h}(X_{t+h}-\bar X_n)(X_t-\bar X_n)$, and
$\hat\rho(h)=\hat\gamma(h)/\hat\gamma(0)$. An **ARMA$(p,q)$ process** is a
weakly stationary solution of $\varphi(B)X_t=\theta(B)Z_t$ with $B$ the
backward shift, $(Z_t)$ white noise of variance $\sigma^2$,
$\varphi(z)=1-\varphi_1z-\cdots-\varphi_pz^p$, and
$\theta(z)=1+\theta_1z+\cdots+\theta_qz^q$. Write $\Rightarrow$ for convergence
in distribution and $\to_P$ for convergence in probability.

### Time series, stochastic processes, and spatial data

* **106.1. Martingale central limit theorem.** Let $X_{n,k}$,
  $1\le k\le k_n$, be a triangular array of square-integrable martingale
  differences relative to filtrations $\mathcal F_{n,k}$. If
  $$\sum_{k=1}^{k_n}\mathbb E[X_{n,k}^2\mid\mathcal F_{n,k-1}]\to_P\sigma^2
  \quad\text{and}\quad
  \sum_{k=1}^{k_n}\mathbb E[X_{n,k}^2\,1_{\{|X_{n,k}|>\varepsilon\}}
  \mid\mathcal F_{n,k-1}]\to_P0$$
  for every $\varepsilon>0$, then $\sum_kX_{n,k}\Rightarrow N(0,\sigma^2)$.
  The central limit theorems of the three libraries are Mathlib's
  independent identically distributed one and consequences of it, such as
  TauCeti's renewal central limit theorem; there is no triangular-array,
  Lindeberg, or martingale-difference version.

* **106.2. Wold decomposition and causal autoregression.** Let
  $\varepsilon_t=X_t-P_{t-1}X_t$ and suppose
  $\sigma^2=\mathbb E\varepsilon_t^2>0$. There are coefficients $\psi_j$ with
  $\psi_0=1$ and $\sum_j\psi_j^2<\infty$, and a process $(V_t)$ orthogonal to
  every innovation and lying in the remote past
  $\bigcap_m\overline{\mathop{\mathrm{span}}}\{X_s:s\le m\}$, such that
  $X_t=\sum_{j\ge0}\psi_j\varepsilon_{t-j}+V_t$ in $L^2$. If $(Z_t)$ is white
  noise of variance $\sigma^2>0$ and $1-\varphi_1z-\cdots-\varphi_pz^p$ has
  no zero in the closed unit disk, then
  $X_t=\varphi_1X_{t-1}+\cdots+\varphi_pX_{t-p}+Z_t$ has a unique weakly
  stationary solution, $X_t=\sum_{j\ge0}\psi_jZ_{t-j}$ with
  $\sum_j|\psi_j|<\infty$, and $Z_t=X_t-P_{t-1}X_t$. Mathlib provides
  orthogonal projection onto complete subspaces and Gram–Schmidt
  orthogonalization; the innovation sequence, the remote past, and the
  Wold decomposition are not formed.

* **106.4. Bartlett's theorem.** Let
  $X_t-\mu=\sum_{j=-\infty}^\infty\psi_jZ_{t-j}$ with $\sum_j|\psi_j|<\infty$
  and $(Z_t)$ independent identically distributed with mean $0$, variance
  $\sigma^2>0$, and $\mathbb EZ_t^4<\infty$. For each fixed $h$,
  $\sqrt n(\hat\rho(1)-\rho(1),\ldots,\hat\rho(h)-\rho(h))\Rightarrow N(0,W)$
  with
  $$w_{ij}=\sum_{k=1}^\infty\bigl(\rho(k+i)+\rho(k-i)-2\rho(i)\rho(k)\bigr)
  \bigl(\rho(k+j)+\rho(k-j)-2\rho(j)\rho(k)\bigr).$$
  For independent identically distributed observations with finite positive
  variance, $\sqrt n\,\hat\rho(h)\Rightarrow N(0,1)$ for each $h\ge1$, with
  independent limits at any fixed finite set of positive lags. Absent from
  all three libraries.

* **106.6. Periodogram and lag-window estimation.** Let
  $X_t=\sum_j\psi_jZ_{t-j}$ with $\sum_j|\psi_j|<\infty$ and $(Z_t)$
  independent identically distributed with mean $0$ and variance
  $\sigma^2>0$, and suppose $f>0$. For fixed $0<\lambda_1<\cdots<\lambda_m<\pi$
  and Fourier frequencies $\omega_{n,j}=2\pi k/n$ nearest to $\lambda_j$, the
  vector $(I_n(\omega_{n,j})/f(\lambda_j))_{j\le m}$ converges in law to
  independent standard exponential variables; in particular the periodogram
  is not consistent. Let $w$ be a lag window (even, piecewise continuous,
  continuous at $0$, $w(0)=1$, $|w|\le1$, vanishing outside $[-1,1]$) and
  $\hat f_n(\omega)=(2\pi)^{-1}\sum_{|h|\le r}w(h/r)\hat\gamma(h)e^{-ih\omega}$.
  If moreover $\sum_j|\psi_j||j|^{1/2}<\infty$, $\mathbb EZ_t^4<\infty$,
  $r\to\infty$ and $r/n\to0$, then for every $\omega\in[0,\pi]$,
  $\mathbb E\hat f_n(\omega)\to f(\omega)$ and
  $$\frac nr\mathop{\mathrm{Var}}\bigl(\hat f_n(\omega)\bigr)\to
  c_\omega f(\omega)^2\int_{-1}^1w(u)^2\,du,$$
  with $c_\omega=1$ for $0<\omega<\pi$ and $c_\omega=2$ for $\omega\in\{0,\pi\}$,
  so $\hat f_n(\omega)\to f(\omega)$ in mean square. Mathlib has Fourier
  series on the circle with Parseval's identity; no periodogram or spectral
  estimator is defined in any of the three libraries.

Consider a linear state-space model $x_{t+1}=F_tx_t+w_t$, $y_t=H_tx_t+v_t$,
with Gaussian white noises $w_t,v_t$ of covariances $Q_t,R_t$, independent of
each other and of a Gaussian initial state, and write $x_{t\mid s}$ and
$P_{t\mid s}$ for the conditional mean and covariance of $x_t$ given
$y_1,\ldots,y_s$.

* **106.7. Kalman filter.** Suppose every innovation covariance
  $\Sigma_t=H_tP_{t\mid t-1}H_t^\top+R_t$ is nonsingular, with $x_{1\mid0}$ and
  $P_{1\mid0}$ the mean and covariance of the initial state. Then the
  conditional law of $x_t$ given $y_1,\ldots,y_t$ is Gaussian with mean and
  covariance
  $$x_{t\mid t}=x_{t\mid t-1}+K_t(y_t-H_tx_{t\mid t-1}),\qquad
  P_{t\mid t}=P_{t\mid t-1}-K_tH_tP_{t\mid t-1},$$
  where $K_t=P_{t\mid t-1}H_t^\top\Sigma_t^{-1}$, and
  $x_{t+1\mid t}=F_tx_{t\mid t}$, $P_{t+1\mid t}=F_tP_{t\mid t}F_t^\top+Q_t$. The
  innovations $y_t-H_tx_{t\mid t-1}$, $t\le n$, are independent with laws
  $N(0,\Sigma_t)$, and the density of $(y_1,\ldots,y_n)$ is the product of
  their densities. TauCeti's Gaussian conditioning theorem (regular
  conditional law of one block of a Gaussian vector given another, for
  positive-semidefinite covariance, with generalized Schur-complement
  covariance) gives the measurement update at $t=1$ as an instance. Missing are the recursion in $t$, which requires conditioning
  on a growing observation vector, and the independence and factorization
  of the innovations; these are within reach by induction from the
  Gaussian conditioning, affine-image, and independence results.

* **106.11. Moving-block bootstrap.** Let $(X_t)$ be strictly stationary
  with mean $\mu$ and strong mixing coefficients
  $\alpha(k)=\sup|P(A\cap B)-P(A)P(B)|$ over $A\in\sigma(X_s:s\le0)$ and
  $B\in\sigma(X_s:s\ge k)$, and suppose that for some $\delta>0$,
  $\mathbb E|X_1|^{2+\delta}<\infty$ and
  $\sum_k\alpha(k)^{\delta/(2+\delta)}<\infty$. Then the long-run variance
  $\sigma_\infty^2=\sum_k\gamma(k)$ is finite; assume it is positive. For
  block length $b\le n$ with $b\to\infty$ and $b/n\to0$, let
  $\ell=\lfloor n/b\rfloor$, and let $\bar X_n^*$ be the mean of $\ell$
  blocks $(X_i,\ldots,X_{i+b-1})$ with starting indices drawn independently
  and uniformly from $\{1,\ldots,n-b+1\}$, with $P^*$, $\mathbb E^*$ given the
  data. Then
  $$\sup_x\Bigl|P^*\bigl(\sqrt{\ell b}\,(\bar X_n^*-\mathbb E^*\bar X_n^*)\le
  x\bigr)-P\bigl(\sqrt n\,(\bar X_n-\mu)\le x\bigr)\Bigr|\to_P0,$$
  and both laws are asymptotically $N(0,\sigma_\infty^2)$. Mixing
  coefficients and resampling are absent from all three libraries.

### Mean estimation and innovation likelihoods

* **106.12. Long-run variance of a sample mean.** For a stationary process
  with absolutely summable autocovariances,
  $n\mathop{\mathrm{Var}}(\bar X_n)\to v=\sum_h\gamma(h)=2\pi f(0)$. For a
  linear process $X_t-\mu=\sum_{j\ge0}\psi_j\varepsilon_{t-j}$ with absolutely
  summable coefficients and independent identically distributed innovations
  of mean zero and finite variance $\sigma^2$,
  $\sqrt n(\bar X_n-\mu)\Rightarrow N(0,v)$ with $v=\sigma^2(\sum_j\psi_j)^2$;
  if $v>0$ and $\hat v_n\to_Pv$, the interval
  $\bar X_n\pm z(\hat v_n/n)^{1/2}$, with $z$ the upper $\alpha/2$ point of
  $N(0,1)$, has asymptotic coverage $1-\alpha$. Mathlib's variance of a
  finite sum as a double sum of covariances gives the first statement by
  reindexing and dominated convergence, which are not carried out; TauCeti's
  mean-square error of a sample mean under pairwise independence is the
  uncorrelated case. The central limit theorem for linear processes is
  missing from all three libraries.

### Spectral representation and linear prediction

A complex function $\gamma$ on $\mathbb Z$ is **nonnegative definite** when
$\sum_{r,s}a_r\gamma(r-s)\bar a_s\ge0$ for all finite families of complex
$a_r$.

* **106.14. Herglotz theorem and rational spectral densities.** A complex
  function $\gamma$ on $\mathbb Z$ is the autocovariance function of a weakly
  stationary (complex-valued) process if and only if it is Hermitian and nonnegative
  definite, and if and only if
  $\gamma(h)=\int_{(-\pi,\pi]}e^{ih\nu}\,dF(\nu)$ for a right-continuous,
  nondecreasing, bounded $F$ on $[-\pi,\pi]$ with $F(-\pi)=0$; $F$ is
  uniquely determined by $\gamma$. If $\sum_h|\gamma(h)|<\infty$, then $F$
  has the continuous density $f$. If $\varphi$ and $\theta$ have no common
  zeros and $\varphi$ has no zero on the unit circle, the ARMA equation has a
  unique stationary solution, with spectral density
  $$f(\lambda)=\frac{\sigma^2}{2\pi}\,
  \frac{|\theta(e^{-i\lambda})|^2}{|\varphi(e^{-i\lambda})|^2}.$$
  TauCeti proves Herglotz's equivalence between positive definiteness on
  $\mathbb Z$ and representation by a finite positive measure on the unit
  circle, and realizes positive-definite kernels as Gram kernels in a
  Hilbert space. Missing are the realization as the autocovariance of a
  stationary process (for instance a Gaussian one, through Mathlib's
  projective limit of finite-dimensional laws, or a random-phase process),
  the density for summable $\gamma$, and the ARMA existence and spectral
  density; uniqueness follows from TauCeti's injectivity of the
  Fourier–Stieltjes transform on Pontryagin duals but is not stated.

* **106.16. Kolmogorov's formula for the prediction error.** Let $F$ be the
  spectral distribution function of $(X_t)$ and $f$ the density of its
  absolutely continuous part. The one-step prediction error from the
  infinite past, $\sigma^2=\mathbb E(X_t-P_{t-1}X_t)^2$, is
  $$\sigma^2=2\pi\exp\Bigl\{\frac1{2\pi}\int_{-\pi}^{\pi}\log f(\lambda)
  \,d\lambda\Bigr\},$$
  read as $0$ when the integral is $-\infty$; thus $X_t$ is linearly
  predictable without error from its past if and only if
  $\int\log f=-\infty$. This is the Szegő infimum theorem, which none of the
  three libraries proves; TauCeti's Hardy-space Toeplitz operators are not
  connected to prediction.

### ARMA estimation, conditional heteroscedasticity, and Markov chains

Write $\beta=(\varphi_1,\ldots,\varphi_p,\theta_1,\ldots,\theta_q)$ and
$g(\lambda;\beta)=|\theta(e^{-i\lambda})|^2/|\varphi(e^{-i\lambda})|^2$. The
**Whittle estimator** minimizes $n^{-1}\sum_jI_n(\omega_j)/g(\omega_j;\beta)$
over the Fourier frequencies $\omega_j\in(-\pi,\pi]$. A **GARCH$(1,1)$
process** solves $X_t=\sigma_t\varepsilon_t$,
$\sigma_t^2=\alpha_0+\alpha_1X_{t-1}^2+\beta_1\sigma_{t-1}^2$, with
$(\varepsilon_t)$ independent identically distributed of mean $0$ and
variance $1$, $\alpha_0>0$, $\alpha_1,\beta_1\ge0$; it is **nonanticipative**
when $\varepsilon_t$ is independent of $\{\sigma_s^2:s\le t\}$.

* **106.17. Asymptotic covariance of ARMA estimators.** Let $(X_t)$ be an
  ARMA$(p,q)$ process with independent identically distributed innovations
  of mean $0$ and variance $\sigma^2>0$, not necessarily Gaussian, and
  suppose $\varphi(z)\theta(z)\ne0$ for $|z|\le1$, $\varphi$ and $\theta$
  have no common zeros, and $(\varphi_p,\theta_q)\ne(0,0)$. Then the
  Gaussian maximum likelihood, least-squares, and Whittle estimators, each
  computed over parameters with these properties, are strongly consistent,
  the innovation-variance estimators converge almost surely to $\sigma^2$,
  and each of the three estimators satisfies
  $$\sqrt n\,(\hat\beta_n-\beta)\Rightarrow N\bigl(0,W(\beta)^{-1}\bigr),\qquad
  W(\beta)=\frac1{4\pi}\int_{-\pi}^{\pi}
  \nabla_\beta\log g(\lambda;\beta)\,\nabla_\beta\log g(\lambda;\beta)^\top
  \,d\lambda.$$
  For an autoregression $W(\beta)^{-1}=\sigma^2\Gamma_p^{-1}$, with
  $\Gamma_p=(\gamma(i-j))_{i,j\le p}$. Absent from all three libraries; it
  needs central limit theorems for dependent data and a pointwise ergodic
  theorem, of which Mathlib has only the maximal ergodic inequality from
  which the pointwise theorem is classically derived.

* **106.18. Stationarity of GARCH$(1,1)$.** Let
  $\gamma=\mathbb E\log(\beta_1+\alpha_1\varepsilon_0^2)\in[-\infty,\infty)$. If
  $\gamma<0$, the series
  $$\sigma_t^2=\alpha_0\Bigl(1+\sum_{n=1}^\infty\prod_{j=1}^n
  (\beta_1+\alpha_1\varepsilon_{t-j}^2)\Bigr)$$
  converges almost surely and, with $X_t=\sigma_t\varepsilon_t$, defines the
  unique strictly stationary solution; if $\gamma\ge0$, there is no
  strictly stationary solution. A nonanticipative weakly stationary solution
  with finite second moments exists if and only if $\alpha_1+\beta_1<1$; it
  is then the solution above, and $(X_t)$ is weak white noise of variance
  $\alpha_0/(1-\alpha_1-\beta_1)$. Absent from all three libraries.
  Because the innovations are independent, the almost-sure convergence and
  uniqueness need only Mathlib's strong law for independent identically
  distributed variables; nonexistence in the boundary case $\gamma=0$
  needs the oscillation of a nondegenerate mean-zero random walk, which
  none of the three libraries proves.

### Spatial data, point patterns, and Gaussian processes

* **106.21. Stein's prediction theorem.** Let $h_1,h_2,\ldots$ be random
  variables, linearly independent under a covariance $k_0$, with closed
  linear span $\mathcal H$ in $L^2$ under $k_0$. For $\psi\in\mathcal H$ and
  $i=0,1$, let $e_i(\psi,n)$ be the error of the best linear predictor of
  $\psi$ from $h_1,\ldots,h_n$ computed as if the covariance were $k_i$, and
  write $\mathbb E_i$ for expectation under the centred Gaussian law with
  covariance $k_i$. If these two Gaussian laws of $(h_1,h_2,\ldots)$ are
  equivalent, then, with suprema over $\psi$ with
  $\mathbb E_0e_0(\psi,n)^2>0$,
  $$\sup_\psi\Bigl|\frac{\mathbb E_0e_1(\psi,n)^2}{\mathbb E_0e_0(\psi,n)^2}
  -1\Bigr|\to0,\qquad
  \sup_\psi\Bigl|\frac{\mathbb E_1e_0(\psi,n)^2}{\mathbb E_0e_0(\psi,n)^2}
  -1\Bigr|\to0,$$
  and the roles of $k_0$ and $k_1$ may be exchanged. Equivalence and
  singularity of Gaussian measures (Feldman–Hájek) are absent from all three
  libraries, and no Gaussian process with a prescribed covariance is
  constructed.

### Covariance models for random fields

A complex function $K$ on $\mathbb R^d$ is **positive definite** when
$\sum_{j,k}c_j\bar c_kK(x_j-x_k)\ge0$ for all finite families of points and
complex coefficients. A field on $\mathbb R$ is **mean-square differentiable**
when its difference quotients converge in $L^2$, and $m$ times so when this
holds iteratively.

* **106.24. Bochner's theorem and the Matérn family.** A function $K$ on
  $\mathbb R^d$ is the autocovariance of a weakly stationary, mean-square
  continuous, complex random field if and only if
  $K(x)=\int e^{i\omega\cdot x}\,F(d\omega)$ for a finite positive measure $F$.
  On $\mathbb R$ the field is $m$ times mean-square differentiable if and
  only if $K$ has a finite derivative of order $2m$ at $0$, equivalently
  $\int\omega^{2m}F(d\omega)<\infty$, and for $m=1$ the derivative has
  autocovariance $-K''$. The Matérn covariance
  $K(x)=\phi(\alpha|x|)^\nu\mathcal K_\nu(\alpha|x|)$, $\phi,\alpha,\nu>0$, with
  $\mathcal K_\nu$ the modified Bessel function of the second kind, is
  positive definite on every $\mathbb R^d$ with isotropic spectral density
  proportional to $(\alpha^2+|\omega|^2)^{-\nu-d/2}$; on $\mathbb R$ the field
  is $m$ times mean-square differentiable if and only if $\nu>m$, and for
  $\nu=m+1/2$ the covariance is $e^{-\alpha|x|}$ times a polynomial of
  degree $m$ in $|x|$. TauCeti proves Bochner's theorem on $\mathbb R^d$ as
  the equivalence between continuous positive-definite functions and
  Fourier transforms of finite positive measures, and its Cauchy
  characteristic function gives the exponential case on $\mathbb R$.
  Missing are the random-field realization, the differentiability
  criterion, and the Matérn family, whose function $\mathcal K_\nu$ is not
  defined in any of the three libraries.

### Survival analysis and counting processes

Let $T$ be a failure time and $C$ an independent censoring time, observed as
$\tilde T=\min(T,C)$ and $\delta=1_{\{T\le C\}}$ in independent copies. Let
$N(t)=1_{\{\tilde T\le t,\delta=1\}}$, $Y(t)=1_{\{\tilde T\ge t\}}$,
$\Lambda(t)=\int_0^t\lambda$ the cumulative hazard, $y(u)=\mathbb P(\tilde T\ge u)$,
and assume $y(\tau)>0$. At an observed failure time $t_i$ there are $d_i$
failures and $n_i$ subjects at risk. $D[0,\tau]$ is the Skorokhod space. In
the **Cox model** the conditional hazard is
$\lambda(t\mid Z)=\lambda_0(t)\exp(\beta\cdot Z)$, with partial likelihood
$$L(\beta)=\prod_{\delta_i=1}
\frac{\exp(\beta\cdot Z_i)}{\sum_{j:\tilde T_j\ge\tilde T_i}\exp(\beta\cdot Z_j)}.$$

* **106.28. Nelson–Aalen estimator.** For a continuous failure distribution,
  the estimator $\hat\Lambda(t)=\sum_{t_i\le t}d_i/n_i$ satisfies: from $n$
  independent copies, $\sqrt n(\hat\Lambda-\Lambda)$ converges weakly in
  $D[0,\tau]$ to a centred Gaussian martingale $W$ with independent
  increments and variance function $\int_0^td\Lambda(u)/y(u)$. TauCeti's
  hazard representation identifies $\Lambda$ and $S=e^{-\Lambda}$ for
  absolutely continuous laws; no estimator, counting-process martingale, or
  Skorokhod space is defined in any of the three libraries.

* **106.29. Kaplan–Meier estimator.** Under the assumptions of 106.28, the
  product-limit estimator $\hat S(t)=\prod_{t_i\le t}(1-d_i/n_i)$ satisfies
  $\sqrt n(\hat S-S)\Rightarrow G=-SW$ weakly in $D[0,\tau]$, so
  $\mathop{\mathrm{Var}}G(t)=S(t)^2\int_0^td\Lambda(u)/y(u)$; Greenwood's
  estimator
  $\hat S(t)^2\sum_{t_i\le t}d_i/(n_i(n_i-d_i))$, multiplied by $n$,
  converges in probability to $\mathop{\mathrm{Var}}G(t)$ uniformly on
  $[0,\tau]$. Absent from all three libraries.

* **106.30. Cox partial likelihood.** Let $(T_i,C_i,Z_i)$ be independent
  copies of $(T,C,Z)$ with bounded $Z\in\mathbb R^p$, $T$ of conditional
  hazard $\lambda(t\mid Z)$ with $\Lambda_0(\tau)<\infty$, and $T,C$
  conditionally independent given $Z$. Suppose $P(\tilde T\ge\tau)>0$,
  restrict the partial likelihood to failures in $[0,\tau]$, and let
  $\bar e(u)=\mathbb E[Y(u)Ze^{\beta\cdot Z}]/\mathbb E[Y(u)e^{\beta\cdot Z}]$
  at the true $\beta$. If
  $\mathcal I=\mathbb E\int_0^\tau(Z-\bar e(u))^{\otimes2}\,dN(u)$ is positive
  definite, the maximizer $\hat\beta$ satisfies $\hat\beta\to_P\beta$ and
  $\sqrt n(\hat\beta-\beta)\Rightarrow N(0,\mathcal I^{-1})$; $\mathcal I$ is the
  efficient information in the multiplicative intensity model, and for a
  group indicator the score test of $\beta=0$ is the log-rank test. Absent
  from all three libraries.

### Counting-process martingales and regression for hazards

Let $N=(N_1,\ldots,N_k)$ be a multivariate counting process, adapted to a
filtration, with no simultaneous jumps and intensities $\lambda_h$, so that
$M_h=N_h-\int_0^\cdot\lambda_h\,ds$ are local square-integrable martingales.

* **106.34. Rebolledo's martingale central limit theorem.** For each $n$ let
  $N^{(n)}$ be a $k_n$-variate counting process as above with intensities
  $\lambda_h^{(n)}$, let $H^{(n)}=(H^{(n)}_{jh})$ be a $k\times k_n$ matrix of
  locally bounded predictable processes, and set
  $M_j^{(n)}=\sum_h\int_0^\cdot H^{(n)}_{jh}(dN_h^{(n)}-\lambda_h^{(n)}\,ds)$. Let
  $V$ be a continuous deterministic function on $[0,\tau]$ with values in the
  positive semidefinite $k\times k$ matrices, $V(0)=0$, and positive
  semidefinite increments, and let $M^{(\infty)}$ be the continuous centred
  Gaussian martingale with independent increments
  $M^{(\infty)}(t)-M^{(\infty)}(s)\sim N(0,V(t)-V(s))$. If for all $t\le\tau$,
  all $j,j'$, and all $\varepsilon>0$,
  $$\sum_h\int_0^tH_{jh}^{(n)}H_{j'h}^{(n)}\lambda_h^{(n)}\,ds\to_PV_{jj'}(t),
  \qquad
  \sum_h\int_0^t\bigl(H_{jh}^{(n)}\bigr)^2
  1_{\{|H_{jh}^{(n)}|>\varepsilon\}}\lambda_h^{(n)}\,ds\to_P0,$$
  then $M^{(n)}\Rightarrow M^{(\infty)}$ in $D[0,\tau]^k$. Continuous-time
  compensators, stochastic integrals against counting-process martingales,
  and weak convergence in the Skorokhod space are absent from all three
  libraries; TauCeti's renewal counting processes are treated through their
  arrival times, not through compensators.

### Sequential analysis, change detection, and anytime-valid inference

Let $f_0,f_1$ be single-observation densities under two simple hypotheses
and $\Lambda_n=\prod_{i\le n}f_1(X_i)/f_0(X_i)$. The **sequential probability
ratio test** with $0<A<1<B$ samples while $A<\Lambda_n<B$, and at the first
exit time $N$ rejects $H_0$ if $\Lambda_N\ge B$ and accepts it if
$\Lambda_N\le A$.

* **106.37. Sequential probability ratio test.** Let the observations be
  independent with density $f_i$ under $\mathbb P_i$, and suppose
  $0<\mathbb E_i|\log(f_1/f_0)|<\infty$ and $\mathbb P_i(f_1\ne f_0)>0$ for
  $i=0,1$. Then $\mathbb E_iN<\infty$ and, by Wald's identity,
  $\mathbb E_iN=\mathbb E_i\log\Lambda_N/\mathbb E_i\log(f_1/f_0)$. With
  $\alpha=\mathbb P_0(\text{reject }H_0)$ and
  $\beta=\mathbb P_1(\text{accept }H_0)$,
  $$B\le\frac{1-\beta}\alpha,\qquad A\ge\frac\beta{1-\alpha}.$$
  Among all tests, sequential or of fixed sample size, with type I error at
  most $\alpha$ and type II error at most $\beta$, the test minimizes both
  $\mathbb E_0N$ and $\mathbb E_1N$ (Wald and Wolfowitz). Mathlib's optional
  sampling covers only bounded stopping times. Statlib proves Wald's
  identity for integrable stopping times of independent identically
  distributed sequences, the likelihood-ratio density of the laws stopped
  at a stopping time, and the identity $\mathbb E_\mu[N]\,\mathrm{KL}(\mu,\nu)$
  for the Kullback–Leibler divergence of the stopped laws, which supplies
  the information lower bound used for the optimality. No sequential test
  is defined in any of the three libraries; the finiteness of
  $\mathbb E_iN$, the error bounds, and the Wald–Wolfowitz optimality are
  absent.

* **106.38. Ville's inequality and e-values.** If $(M_n)_{n\ge0}$ is a
  nonnegative supermartingale with $M_0\le1$, then for every
  $\alpha\in(0,1)$,
  $$\mathbb P\Bigl(\sup_{n\ge0}M_n\ge\frac1\alpha\Bigr)\le\alpha.$$
  If $E_1,E_2,\ldots$ are nonnegative and adapted with
  $\mathbb E[E_n\mid\mathcal F_{n-1}]\le1$ under every law in a null
  hypothesis, then $M_n=E_1\cdots E_n$, $M_0=1$, is a nonnegative
  supermartingale under each such law, $M_\tau$ is an e-value (nonnegative
  with expectation at most $1$ under the null) for every almost surely
  finite stopping time $\tau$, and rejecting at the first $n$ with
  $M_n\ge1/\alpha$ has level $\alpha$. Mathlib's Doob maximal inequality
  for nonnegative submartingales, which TauCeti extends to general linearly
  ordered time, gives the bound for nonnegative martingales on each finite
  horizon. Statlib defines e-variables for a set of laws, with convexity,
  closure under $\liminf$, products for product laws, and the existence of
  the numeraire e-variable. The supermartingale case follows by a short
  argument: optional stopping at the bounded time
  $\min(n,\tau_{1/\alpha})$, with $\tau_{1/\alpha}$ the hitting time of
  $[1/\alpha,\infty)$, gives $\mathbb P(\max_{k\le n}M_k\ge1/\alpha)\le\alpha$,
  and monotone continuity of measure removes the horizon. Neither step, nor
  the product supermartingale and the e-value consequences for running
  products of conditional e-values, is stated in any of the three
  libraries.

* **106.39. CUSUM and the Brownian bridge.** Let $X_1,X_2,\ldots$ be
  independent with a common law of mean $\mu_0$ and variance
  $\sigma^2\in(0,\infty)$, and $S_k=\sum_{t\le k}(X_t-\mu_0)$. Then
  $$\frac1{\sigma\sqrt n}\max_{1\le k\le n}\Bigl|S_k-\frac knS_n\Bigr|
  \Rightarrow\sup_{t\in[0,1]}|B^0(t)|,$$
  with $B^0$ a Brownian bridge. Donsker's invariance principle and the
  Brownian bridge are absent from all three libraries.

### Wald's identity, random sample sizes, and fixed-width intervals

In the setting of 106.37 write $Z_i=\log(f_1(X_i)/f_0(X_i))$ and
$S_n=Z_1+\cdots+Z_n$, with the observations independent of a common law
$P_\theta$, not necessarily one of the hypotheses. The **operating
characteristic** is $L(\theta)=P_\theta(\text{accept }H_0)$.

* **106.41. Wald's fundamental identity and the operating characteristic.**
  Suppose $P_\theta(Z>0)>0$, $P_\theta(Z<0)>0$, and
  $\phi(t)=\mathbb E_\theta e^{tZ}<\infty$ for all real $t$. Then
  $\mathbb E_\theta[e^{tS_N}\phi(t)^{-N}]=1$ for every real $t$ with
  $\phi(t)\ge1$. If $\mathbb E_\theta Z\ne0$, there is exactly one real
  $h\ne0$ with $\phi(h)=1$, and $\mathbb E_\theta e^{hS_N}=1$ and
  $\mathbb E_\theta N=\mathbb E_\theta S_N/\mathbb E_\theta Z$. If
  $S_N\in\{\log A,\log B\}$ almost surely, then
  $$L(\theta)=\frac{B^h-1}{B^h-A^h},\qquad
  \mathbb E_\theta N=\frac{L(\theta)\log A+(1-L(\theta))\log B}
  {\mathbb E_\theta Z}.$$
  Mathlib has moment-generating functions and their multiplicativity over
  independent sums, and Statlib proves Wald's identity
  $\mathbb E S_N=\mathbb EN\,\mathbb EZ$ for integrable stopping times of
  independent identically distributed sequences. Optional stopping of the
  exponential martingale at the unbounded time $N$, the fundamental
  identity, the existence of $h$, and the operating characteristic are
  missing from all three libraries.

* **106.42. Anscombe's theorem.** Let $X_1,X_2,\ldots$ be independent and
  identically distributed with mean $\mu$ and variance
  $\sigma^2\in(0,\infty)$, and let $N_a$ be positive integer random variables
  with $N_a/a\to_Pk\in(0,\infty)$. Then
  $(S_{N_a}-N_a\mu)/(\sigma\sqrt{N_a})\Rightarrow N(0,1)$, with no
  independence required between $N_a$ and the observations. More generally,
  if $Y_n\Rightarrow Y$ and $(Y_n)$ is uniformly continuous in probability
  (for each $\varepsilon>0$ some $\delta>0$ gives
  $P(\max_{0\le j\le n\delta}|Y_{n+j}-Y_n|>\varepsilon)<\varepsilon$ for all
  $n$), then $Y_{N_a}\Rightarrow Y$. Random-index limit theorems are absent
  from all three libraries; TauCeti's strong law and central limit theorem
  for the renewal count, proved by inverting the limit theorems for the
  arrival times, are the nearest results.

### Optimal change detection

For a change point $\nu\ge0$, under $P_\nu$ the observations
$X_1,\ldots,X_\nu$ have density $f_0$ and $X_{\nu+1},\ldots$ have density $f_1$,
all independent; $P_\infty$ has no change. With $L_n=f_1(X_n)/f_0(X_n)$, the
**CUSUM statistic** is $V_n=\max_{0\le k<n}\prod_{i=k+1}^nL_i$ and the CUSUM
procedure stops at $T_{\mathrm{CS}}(A)=\inf\{n\ge1:V_n\ge A\}$. **Lorden's
worst-case delay** is
$\mathop{\mathrm{ESADD}}(T)=\sup_\nu\mathop{\mathrm{ess\,sup}}
\mathbb E_\nu[(T-\nu)^+\mid X_1,\ldots,X_\nu]$, $\mathcal C_\gamma$ is the class
of stopping times with $\mathbb E_\infty T\ge\gamma$, and
$I=\mathbb E_0\log L_1$.

* **106.44. Optimality of CUSUM.** For every $A>0$,
  $\mathbb E_\infty T_{\mathrm{CS}}(A)\ge A$, and the worst-case delay of the
  CUSUM procedure equals $\mathbb E_0T_{\mathrm{CS}}(A)$. If $\gamma>1$ and
  $A_\gamma$ is chosen, randomizing on the boundary if necessary, so that
  $\mathbb E_\infty T_{\mathrm{CS}}(A_\gamma)=\gamma$, then
  $\mathop{\mathrm{ESADD}}(T_{\mathrm{CS}}(A_\gamma))
  =\inf_{T\in\mathcal C_\gamma}\mathop{\mathrm{ESADD}}(T)$ (Moustakides). If
  $0<I<\infty$, then as $\gamma\to\infty$
  $$\inf_{T\in\mathcal C_\gamma}\mathop{\mathrm{ESADD}}(T)\sim
  \mathbb E_0T_{\mathrm{CS}}(A_\gamma)\sim\frac{\log\gamma}I$$
  (Lorden), with the same first-order asymptotics for the threshold
  $A=\gamma$. Optimal-stopping theory and change-detection procedures are
  absent from all three libraries; Mathlib's Kullback–Leibler divergence
  defines $I$, and Statlib's Kullback–Leibler and Rényi divergences of
  independent identically distributed laws stopped at a stopping time,
  without a change point, are ingredients of lower bounds on the delay.

### Extreme-value statistics

Let $M_n=\max(X_1,\ldots,X_n)$ for independent copies of a variable with
distribution function $F$, and $x_F=\sup\{x:F(x)<1\}$. The **generalized
extreme-value laws** are $G_\gamma(x)=\exp(-(1+\gamma x)^{-1/\gamma})$ for
$\gamma\ne0$ and $1+\gamma x>0$, and $G_0(x)=\exp(-e^{-x})$. The **generalized
Pareto laws** are $H_{\gamma,\sigma}(y)=1-(1+\gamma y/\sigma)^{-1/\gamma}$ for
$\gamma\ne0$ and $H_{0,\sigma}(y)=1-e^{-y/\sigma}$, on the $y>0$ with
$1+\gamma y/\sigma>0$.

* **106.46. Fisher–Tippett–Gnedenko theorem.** The nondegenerate
  distributional limits of $(M_n-b_n)/a_n$, $a_n>0$, are exactly the laws
  $G_\gamma(ax+b)$ with $a>0$ and $b,\gamma\in\mathbb R$. For $\gamma>0$, $F$
  is in the domain of attraction of $G_\gamma$ if and only if $x_F=\infty$
  and $(1-F(tx))/(1-F(t))\to x^{-1/\gamma}$ for $x>0$ as $t\to\infty$; for
  $\gamma<0$, if and only if $x_F<\infty$ and
  $(1-F(x_F-(tx)^{-1}))/(1-F(x_F-t^{-1}))\to x^{1/\gamma}$; for $\gamma=0$, if
  and only if there is a positive $a$ with
  $(1-F(t+xa(t)))/(1-F(t))\to e^{-x}$ for real $x$ as $t\uparrow x_F$, and
  one may take the mean excess
  $a(t)=\int_t^{x_F}(1-F(s))\,ds/(1-F(t))$. The von Mises condition (a
  positive density $f$ near $x_F$ with
  $(d/dx)((1-F)/f)\to0$ as $x\uparrow x_F$) is sufficient for $\gamma=0$.
  TauCeti defines the generalized extreme-value family, with distribution
  function $G_\gamma((x-m)/s)$ and the Gumbel law at $\gamma=0$, proves its
  max-stability (the maximum of $n$ independent copies has the same shape,
  with explicit scale and location), defines the Weibull law, and proves
  that the maximum of $n$ independent identically distributed variables has
  distribution function $F^n$. Regular variation, the convergence-of-types
  lemma, the classification of the limits, and the domain-of-attraction
  criteria are absent from all three libraries.

* **106.47. Excesses over high thresholds.** $F$ lies in the domain of
  attraction of $G_\gamma$ if and only if there is a positive scale
  $\sigma(u)$ with
  $$\sup_{y\ge0}\Bigl|
  \mathbb P(X-u\le y\mid X>u)-H_{\gamma,\sigma(u)}(y)\Bigr|\to0
  \qquad(u\uparrow x_F).$$
  The comparison includes the terminal jump and all larger excesses when
  the upper endpoint is finite; the generalized Pareto distribution function
  is extended by one beyond its finite endpoint. TauCeti defines the generalized Pareto family with distribution function
  $H_{\gamma,\sigma}$ and proves its threshold stability: the excess over a
  threshold $v$ with $\sigma+\gamma v>0$, given exceedance, is generalized
  Pareto with scale $\sigma+\gamma v$ and the same shape. The equivalence
  with the domain of attraction is absent from all three libraries.

For a strictly stationary sequence with maximum $M_n$, let $u_n$ satisfy
$n(1-F(u_n))\to\tau\in(0,\infty)$. Condition $D(u_n)$ holds when there are
$\alpha_{n,l}$ with $\alpha_{n,l_n}\to0$ for some $l_n=o(n)$ such that
$|P(\max_{I\cup J}X_i\le u_n)-P(\max_IX_i\le u_n)P(\max_JX_i\le u_n)|
\le\alpha_{n,l}$ for all $I,J\subset\{1,\ldots,n\}$ separated by at least $l$.
Condition $D'(u_n)$ holds when
$\limsup_nn\sum_{j=2}^{\lfloor n/k\rfloor}P(X_1>u_n,X_j>u_n)\to0$ as
$k\to\infty$.

* **106.48. Extremal index.** The sequence has extremal index
  $\theta\in(0,1]$ when, for every $\tau>0$, $P(M_n\le u_n)\to e^{-\theta\tau}$
  for every $(u_n)$ with $n(1-F(u_n))\to\tau$. An independent sequence has
  extremal index $1$; more generally, if $D(u_n)$ and $D'(u_n)$ hold for
  every such sequence and every $\tau>0$, the extremal index is $1$
  (Leadbetter). Absent from all three libraries.

For positive observations the **Hill estimator** is
$H_{k,n}=k^{-1}\sum_{i=1}^k\log X_{(n-i+1)}-\log X_{(n-k)}$. With $U$ the
left-continuous inverse of $1/(1-F)$, a **second-order condition** with
$\gamma>0$ and $\rho<0$ holds when, for some $A$ of constant sign with
$A(t)\to0$,
$(U(tx)/U(t)-x^\gamma)/A(t)\to x^\gamma(x^\rho-1)/\rho$ for $x>0$.

* **106.49. Hill estimator.** If $1-F$ is regularly varying of index
  $-1/\gamma$ with $\gamma>0$, the second-order condition holds, $k\to\infty$,
  $k/n\to0$, and $\sqrt kA(n/k)\to\lambda\in\mathbb R$, then
  $$\sqrt k\,(H_{k,n}-\gamma)\Rightarrow
  N\Bigl(\frac\lambda{1-\rho},\gamma^2\Bigr).$$
  TauCeti's order-statistic laws are supporting material; the Hill
  estimator and regular variation are absent.

### Exceedances and block maxima

* **106.50. Poisson approximation for exceedances.** For independent
  observations, $0\le\tau\le\infty$, and real $u_n$,
  $P(M_n\le u_n)\to e^{-\tau}$ if and only if $n(1-F(u_n))\to\tau$; for finite
  $\tau$ the number of exceedances of $u_n$ then converges in law to a
  Poisson law of mean $\tau$. For $0<\tau<\infty$, levels with
  $n(1-F(u_n))\to\tau$ exist if and only if both
  $\lim_{x\uparrow x_F}F(x)=1$ and $(1-F(x))/(1-F(x-))\to1$ as
  $x\uparrow x_F$; hence the Poisson and geometric laws are in no domain of
  attraction. The forward direction for finite $\tau$ follows by a short
  argument from TauCeti's formula $P(M_n\le u)=F(u)^n$, Mathlib's limit
  $(1+a_n)^n\to e^t$ when $na_n\to t$, and Mathlib's binomial-to-Poisson
  limit theorem; it is not assembled. The converse, the case $\tau=\infty$,
  and the existence criterion for the levels are missing.

## 107. Statistical learning and machine learning

None of Mathlib, TauCeti and Statlib defines a hypothesis class with its
risk, a learning rule, a sequential policy, a Markov decision process, or a
differentially private mechanism, so almost all of this section is missing.
TauCeti specifies multilayer perceptrons with their realizations, but no
approximation, capacity, initialization, or training theorem is proved for
them. Mathlib supplies the infrastructure on which the statements would
be built: the combinatorial VC dimension of finite set families with the
Sauer–Shelah bound, Hoeffding's lemma and inequality, the Azuma–Hoeffding
inequality for conditionally sub-Gaussian increments, reproducing-kernel
Hilbert spaces with Moore's theorem, convex projection in inner product
spaces, the Kullback–Leibler divergence with its chain rule and
data-processing inequality, the Ionescu–Tulcea construction of laws of
interaction, the Banach fixed-point theorem and Neumann series, the binomial
random graph, and circulant matrices. TauCeti adds McDiarmid's
bounded-differences inequality, Bernstein's inequality, the Azuma–Hoeffding
inequality for bounded martingale differences, an operator-norm tail bound
for random matrices with independent sub-Gaussian entries, the Rademacher and
Laplace laws, Pinsker's inequality, Gaussian conditioning, the inverse-Wishart
mean, the Moore–Penrose inverse, the derivative of the softmax map in reduced
coordinates, the Davis–Kahan $\sin\Theta$ theorem, and the graphon form of
the Aldous–Hoover theorem with uniqueness of the mixing measure up to cut
distance zero. Statlib adds the Bayes test between two laws with its Bayes
risk, the Jensen–Shannon divergence, definitions of contiguity, the
divergence of independent observations up to a stopping time with Wald's
identity, the tensorization of the divergence, the Bretagnolle–Huber
inequality, integral forms of the total variation distance, and data
processing for total variation and mutual information. The principal
omissions are VC and Rademacher generalization theory, classification
consistency, kernel and nearest-neighbour rates, graphical-model inference,
approximation and training theory of neural networks, block-model and
random-graph thresholds, bandit regret bounds, reinforcement-learning
convergence and sample complexity, and the composition and lower-bound theory
of differential privacy.

Sources: [mathematical synopsis](SYNOPSIS107.md); [combined coverage inventory](STRUCTURE107.md).

Throughout, $(X,Y),(X_1,Y_1),\ldots$ are independent and identically
distributed, $\mathcal F$ is a class of measurable decision functions, and
for a loss $L$ with values in $[0,1]$ the risk and empirical risk are
$R(f)=\mathbb E[L(Y,f(X))]$ and $R_n(f)=n^{-1}\sum_{i\le n}L(Y_i,f(X_i))$.
For an independent and identically distributed sample $Z_1,\ldots,Z_n$ of
law $P$ write $Pf=\mathbb Ef(Z_1)$ and $P_nf=n^{-1}\sum_if(Z_i)$. The
**empirical Rademacher complexity** on the sample is
$$\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
=\mathbb E_\sigma\Bigl[\sup_{f\in\mathcal F}
n^{-1}\sum_{i=1}^n\sigma_if(Z_i)\Bigr],$$
with independent Rademacher signs $\sigma_i$, and
$\mathop{\mathrm{Rad}}_n=\mathbb E\,\widehat{\mathop{\mathrm{Rad}}}_n$. In
binary classification $\eta(x)=P(Y=1\mid X=x)$ is the regression function and
$R^*$ the Bayes risk. The Kullback–Leibler divergence is written
$D(\cdot\|\cdot)$ or $\mathop{\mathrm{kl}}$.

In the sequential parts, a policy chooses each action from the past actions
and observations, and the law of the interaction is the law on histories
that it determines. A finite discounted Markov decision process has finite
state and action sets, transition law $P(\cdot\mid s,a)$, bounded rewards,
and discount $\gamma\in(0,1)$; $V^\pi$, $Q^\pi$ and $J(\pi)$ are the
discounted values of a policy $\pi$, and $V^\star$, $Q^\star$ the optimal
ones. Data sets are **neighboring** when they differ in one record; a
mechanism $M$ is **$(\varepsilon,\delta)$-differentially private** if
$P(M(D)\in A)\le e^\varepsilon P(M(D')\in A)+\delta$ for every measurable
$A$ and every neighboring pair, and **$\varepsilon$-differentially private**
when $\delta=0$.

### Statistical learning theory

A class of binary classifiers **shatters** a finite set if it realizes every
labelling of it; the **VC dimension** is the largest size of a shattered set.
A class is **agnostic PAC learnable** with sample complexity
$m(\varepsilon,\delta)$ if some rule mapping samples to $\hat f\in\mathcal F$
satisfies, for all $\varepsilon,\delta\in(0,1)$, every law of $(X,Y)$, and
every $n\ge m(\varepsilon,\delta)$, $R(\hat f)\le\inf_{\mathcal F}R+\varepsilon$
with probability at least $1-\delta$; **realizable** PAC learnability asks
this only for laws with $\inf_{\mathcal F}R=0$. The **regret** of a sequence
of decisions is its excess cumulative loss over the best fixed comparator in
hindsight.

* **107.1. Fundamental theorem of statistical learning.** For binary
  classification under $0$–$1$ loss, finite VC dimension, realizable PAC
  learnability, and agnostic PAC learnability are equivalent. There are
  absolute constants $C_1,C_2>0$ such that, for VC dimension
  $1\le v<\infty$, the agnostic sample complexity lies between
  $C_1(v+\log(1/\delta))/\varepsilon^2$ and
  $C_2(v+\log(1/\delta))/\varepsilon^2$, and the realizable one between
  $C_1(v+\log(1/\delta))/\varepsilon$ and
  $C_2(v\log(1/\varepsilon)+\log(1/\delta))/\varepsilon$. For an
  empirical-risk minimizer $\hat f$ over a class of VC dimension $v\ge1$,
  with a universal $C$, for all $n\ge2$ and $\delta\in(0,1)$, with
  probability at least $1-\delta$,
  $$R(\hat f)\le R_n(\hat f)+C\sqrt{\frac{v\log n+\log(1/\delta)}n}.$$
  Mathlib proves the Sauer–Shelah bound for finite set families; missing are
  learning rules and PAC learnability, the uniform deviation bound for VC
  classes (CKMA 07.37), and both directions of the sample-complexity bounds.

* **107.2. Rademacher bound.** For a countable class of measurable
  functions with values in $[0,1]$, or any such class for which the suprema
  below are measurable,
  $\mathbb E\sup_{f}(P_n-P)f\le2\,\mathop{\mathrm{Rad}}_n(\mathcal F)$, and
  likewise with $P-P_n$. With probability at least $1-\delta$,
  $$\sup_{f\in\mathcal F}|(P_n-P)f|
  \le2\mathop{\mathrm{Rad}}_n(\mathcal F)+\sqrt{\frac{\log(2/\delta)}{2n}},$$
  and, with probability at least $1-\delta$,
  $\sup_f(P-P_n)f\le2\widehat{\mathop{\mathrm{Rad}}}_n(\mathcal F)
  +3\sqrt{\log(2/\delta)/(2n)}$. TauCeti supplies the Rademacher law and
  McDiarmid's inequality for finite products, which give the
  high-probability steps; missing are the complexity itself and the
  symmetrization inequality (CKMA 07.33).

* **107.5. Hedge.** For $K$ actions and loss vectors
  $\ell_t\in[0,1]^K$, possibly chosen adaptively, the exponentially weighted
  forecaster with weights $p_t(i)\propto\exp(-\eta\sum_{s<t}\ell_s(i))$ and
  $\eta=\sqrt{8(\log K)/T}$ has regret at most $\sqrt{(T/2)\log K}$ after
  $T$ rounds against the best fixed action. The argument is short from
  Mathlib: bound the logarithm of the ratio of successive normalizing sums by
  Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`)
  applied to $p_t$, and compare the telescoped sum with the weight of the
  best action. No library defines the forecaster or regret.

* **107.6. Split conformal prediction.** Let $S_1,\ldots,S_n$ be
  calibration scores and $S_{n+1}$ the test score, computed by a score
  depending only on an independent training part and on the pair at which
  it is evaluated, and suppose the $n+1$ calibration and test pairs are
  exchangeable conditionally on the training part. For $\alpha\in(0,1)$ put
  $k=\lceil(n+1)(1-\alpha)\rceil$, let $S_{(k)}$ be the $k$th smallest
  calibration score ($+\infty$ if $k>n$), and let
  $C(x)=\{y:s(x,y)\le S_{(k)}\}$. Then
  $\mathbb P(Y_{n+1}\in C(X_{n+1}))\ge1-\alpha$, and the probability is at
  most $1-\alpha+1/(n+1)$ if the $n+1$ scores are almost surely distinct.
  TauCeti defines exchangeability of sequences; the statement follows from
  the uniform distribution of the rank of $S_{n+1}$ among $n+1$
  exchangeable scores, which none of the three libraries states.

* **107.7. No free lunch.** On an infinite feature space, for every $n$,
  every classification rule based on $n$ observations, and every
  $\varepsilon>0$, some distribution with Bayes error zero gives the rule
  expected $0$–$1$ error at least $1/2-\varepsilon$.

### Statistical targets in classification

* **107.8. Bayes classification risk.** For binary labels, the classifier
  $g^*=1_{\{\eta\ge1/2\}}$ minimizes risk, and for every measurable $g$,
  $$R(g)-R(g^*)=\mathbb E\bigl[|2\eta(X)-1|1_{\{g(X)\ne g^*(X)\}}\bigr].$$
  A plug-in rule $\hat g=1_{\{\hat\eta\ge1/2\}}$ built from independent
  training data has conditional excess risk at most
  $2\mathbb E|\hat\eta(X)-\eta(X)|$; if
  $P(|\eta(X)-1/2|\le t)\le Ct^\alpha$ for all $t>0$ and
  $\|\hat\eta-\eta\|_\infty\le\delta$, it is at most $2C\delta^{\alpha+1}$.
  Statlib proves the first assertion in likelihood-ratio form: with the
  conditional laws of $X$ given $Y=0$ and $Y=1$ and the law of $Y$ as prior,
  its Bayes test between the two laws is the rule $1_{\{\eta\ge1/2\}}$, it is
  a Bayes rule for the $0$–$1$ loss, and its Bayes risk is
  $\mathbb E\min(\eta(X),1-\eta(X))$. The excess-risk identity for an
  arbitrary classifier, the plug-in bound, and the margin bound are not
  stated; the identity follows by writing $R(g)=\mathbb E[\eta(X)1_{\{g=0\}}
  +(1-\eta(X))1_{\{g=1\}}]$ and comparing pointwise. The item is the common
  base of 107.11 and 107.14.

### Margins, surrogate losses, and stability

For labels $Y\in\{-1,1\}$ and a real score $h$, write $R(h)=P(Yh(X)\le0)$.
For $\rho>0$ the **ramp loss** is $\Phi_\rho(u)=\min(1,\max(0,1-u/\rho))$
and the **empirical margin loss** is
$\hat R_{n,\rho}(h)=n^{-1}\sum_i\Phi_\rho(Y_ih(X_i))$. A learning algorithm
mapping samples $S$ to predictors $h_S$ is **uniformly $\beta$-stable** if
$|L(h_S,z)-L(h_{S'},z)|\le\beta$ for every point $z$ and all samples
$S,S'$ differing in one point.

* **107.10. Margin bound.** For a class $\mathcal H$ of real functions and
  $\rho>0$, with probability at least $1-\delta$ every $h\in\mathcal H$
  satisfies
  $$R(h)\le\hat R_{n,\rho}(h)+\frac2\rho\mathop{\mathrm{Rad}}_n(\mathcal H)
  +\sqrt{\frac{\log(1/\delta)}{2n}},$$
  and the same holds with $\widehat{\mathop{\mathrm{Rad}}}_n$ in place of
  $\mathop{\mathrm{Rad}}_n$ and $3\sqrt{\log(2/\delta)/(2n)}$ as last term.
  For a kernel ball $\|h\|_{\mathcal H}\le\Lambda$ with $K(x,x)\le r^2$ the
  complexity term is at most $2\Lambda r/(\rho\sqrt n)$. Beyond the
  ingredients of 107.2, the contraction (Talagrand) lemma for Rademacher
  averages is missing.

* **107.11. Comparison inequality for convex surrogates.** Let
  $\Phi:\mathbb R\to[0,\infty)$ be convex and nondecreasing, differentiable
  at $0$ with $\Phi'(0)>0$, let $R_\Phi(h)=\mathbb E\Phi(-Yh(X))$ with
  infimum $R_\Phi^*$, and
  $L_\Phi(x,u)=\eta(x)\Phi(-u)+(1-\eta(x))\Phi(u)$. Every minimizer of
  $u\mapsto L_\Phi(x,u)$ over $[-\infty,\infty]$ has the sign of
  $\eta(x)-1/2$ when this is nonzero, and $u=0$ is a minimizer when
  $\eta(x)=1/2$. If $|\eta(x)-\frac12|^s\le c^s(L_\Phi(x,0)-\inf_uL_\Phi(x,u))$
  for all $x$, with $s\ge1$ and $c>0$, then
  $R(h)-R^*\le2c(R_\Phi(h)-R_\Phi^*)^{1/s}$ for every measurable $h$ with
  $P(h(X)=0)=0$, a condition that cannot be dropped since $R(h)=P(Yh(X)\le0)$
  counts $h(X)=0$ as an error; the
  hinge loss admits $s=1$, $c=1/2$ and the squared hinge $s=2$, $c=1/2$.

* **107.12. Generalization of stable algorithms.** If the algorithm is
  uniformly $\beta$-stable, $(S,z)\mapsto L(h_S,z)$ is measurable, and
  $0\le L(h_S,z)\le M$, then with probability
  at least $1-\delta$,
  $$R(h_S)\le R_n(h_S)+\beta+(2n\beta+M)\sqrt{\frac{\log(1/\delta)}{2n}}.$$
  Regularized empirical risk minimization
  $h_S\in\mathop{\mathrm{argmin}}_h(R_n(h)+\lambda\|h\|_{\mathcal H}^2)$
  over a reproducing-kernel Hilbert space with $K(x,x)\le r^2$ and a loss
  convex and $G$-Lipschitz in the prediction is uniformly stable with
  $\beta\le G^2r^2/(n\lambda)$. The first bound follows from TauCeti's
  McDiarmid inequality applied to $R(h_S)-R_n(h_S)$, whose expectation is at
  most $\beta$ and whose bounded differences are at most $2\beta+M/n$;
  missing are the notion of an algorithm on samples, this argument, and the
  stability of regularized kernel minimization.

### Kernel regression, nearest neighbours, and data splitting

* **107.13. Rate of kernel ridge regression.** In the fixed-design model
  $y_i=f^*(x_i)+\sigma w_i$ with independent standard normal $w_i$, let
  $\hat f$ minimize $(2n)^{-1}\sum_i(y_i-f(x_i))^2+\lambda\|f\|_{\mathcal H}^2$
  over the reproducing-kernel Hilbert space, let
  $\hat\mu_1\ge\cdots\ge\hat\mu_n$ be the eigenvalues of
  $(K(x_i,x_j)/n)$, write $\|g\|_n^2=n^{-1}\sum_ig(x_i)^2$, and fix $R>0$.
  If $\delta_n>0$ satisfies
  $\sqrt{(2/n)\sum_j\min(\delta_n^2,\hat\mu_j)}\le R\delta_n^2/(4\sigma)$
  and $\lambda\ge2\delta_n^2$, then with probability at least
  $1-c_2\exp(-c_3nR^2\delta_n^2/\sigma^2)$, and in expectation,
  $$\|\hat f-f^*\|_n^2\le c_0\inf_{\|f\|_{\mathcal H}\le R}
  \bigl(\|f-f^*\|_n^2+c_1R^2(\delta_n^2+\lambda)\bigr)$$
  with universal constants. Eigenvalue decay $\hat\mu_j\le cj^{-2\alpha}$,
  $\alpha>1/2$, gives $\delta_n^2$ of order
  $(\sigma^2/n)^{2\alpha/(2\alpha+1)}$. Mathlib has the Hilbert space; the
  localized Gaussian complexity argument is missing.

* **107.14. Asymptotics of nearest-neighbour rules.** For the
  $k$-nearest-neighbour rule in $\mathbb R^d$ with independent random tie
  breaking and error probability $L_n$ given the sample, for every
  distribution of $(X,Y)$ the $1$-nearest-neighbour rule has
  $\mathbb EL_n\to\mathbb E[2\eta(X)(1-\eta(X))]=L_{\mathrm{NN}}$ with
  $R^*\le L_{\mathrm{NN}}\le2R^*(1-R^*)$; for fixed odd $k$ the limit
  $L_{k\mathrm{NN}}$ exists, is nonincreasing over odd $k$, and satisfies
  $R^*\le L_{k\mathrm{NN}}\le R^*+1/\sqrt{ke}$; and if $k_n\to\infty$,
  $k_n/n\to0$, then $\mathbb EL_n\to R^*$ for every distribution.

### Foundations, probabilistic modelling, and ensembles

For a pairwise model $p(x)\propto\prod_i\psi_i(x_i)\prod_{\{i,j\}\in E}
\psi_{ij}(x_i,x_j)$ with positive potentials on a finite graph with finite
state spaces, the **local polytope** consists of nonnegative node and edge
tables $b_i,b_{ij}$ with $\sum_{x_i}b_i=1$ and edge tables marginalizing to
the node tables. The **Bethe free energy** is
$$F_B(b)=-\sum_i\sum_{x_i}b_i\log\psi_i
-\sum_{\{i,j\}\in E}\sum_{x_i,x_j}b_{ij}\log\psi_{ij}-H_B(b),\qquad
H_B=\sum_{\{i,j\}\in E}H(b_{ij})-\sum_i(d_i-1)H(b_i),$$
with $d_i$ the degree of $i$, and **belief propagation** iterates
$m_{i\to j}(x_j)\propto\sum_{x_i}\psi_i\psi_{ij}
\prod_{\ell\in N(i)\setminus\{j\}}m_{\ell\to i}(x_i)$ on oriented edges,
with the associated node and edge beliefs.

* **107.16. Consistency of $k$-means.** Let $X$ take values in
  $\mathbb R^d$ with $\mathbb E\|X\|^2<\infty$, let its support contain at
  least $k$ points, and let the criterion $\mathbb E\min_j\|X-c_j\|^2$ have
  a unique minimizing set $C^*$ of $k$ centers. For independent copies
  $X_1,X_2,\ldots$, any minimizer $C_n$ of the empirical criterion over sets
  of at most $k$ centers converges to $C^*$ in Hausdorff distance almost
  surely. Mathlib has the Hausdorff distance only.

* **107.19. Belief propagation and the Bethe free energy.** The beliefs of a
  fixed point of belief propagation lie in the relative interior of the
  local polytope and are a stationary point of $F_B$ restricted to it;
  conversely every stationary point of $F_B$ in that relative interior
  consists of the beliefs of some fixed point.

* **107.20. Consistency of response-independent forests.** With
  $\mathbb EY^2<\infty$ and $m(x)=\mathbb E[Y\mid X=x]$, let weights
  $w_{ni}(x)\ge0$ with $\sum_iw_{ni}(x)=1$ be measurable functions of $x$,
  of $X_1,\ldots,X_n$, and of independent randomness, but not of the
  responses, and put $m_n(x)=\sum_iw_{ni}(x)Y_i$. If
  $\mathbb E\sum_iw_{ni}(X)g(X_i)\le C\mathbb Eg(X)$ for all $n$ and all
  nonnegative bounded measurable $g$, if
  $\mathbb E\sum_iw_{ni}(X)1_{\{\|X_i-X\|>\eta\}}\to0$ for every $\eta>0$,
  and if $\mathbb E\max_iw_{ni}(X)\to0$, then
  $\mathbb E(m_n(X)-m(X))^2\to0$ (Stone's theorem).

### Prediction losses and ensemble structure

* **107.23. Exact belief propagation on a tree.** For the positive pairwise
  model on a tree, the belief-propagation equations have a fixed point,
  unique up to positive scaling of each message and computed by one pass
  from the leaves to a root and back, whose beliefs are the exact node and
  edge marginals. Every member $b$ of the local polytope of a tree is the
  family of marginals of
  $q(x)=\prod_ib_i(x_i)\prod_{\{i,j\}\in E}b_{ij}(x_i,x_j)/(b_i(x_i)b_j(x_j))$,
  with $0/0=0$, and $H(q)=H_B(b)$.

### Boosting and tree splitting

* **107.24. AdaBoost: training error and margins.** On a sample
  $(x_i,y_i)$, $i\le m$, with labels and base classifiers in $\{-1,1\}$,
  AdaBoost starts from uniform weights $D_1$, chooses $h_t$ with weighted
  error $\varepsilon_t$, sets
  $\alpha_t=\frac12\log((1-\varepsilon_t)/\varepsilon_t)$ and
  $D_{t+1}(i)\propto D_t(i)e^{-\alpha_ty_ih_t(x_i)}$, and returns
  $f=\sum_{t\le T}\alpha_th_t$. If $0<\varepsilon_t<1/2$ for all $t$, the
  training error of $\mathop{\mathrm{sign}}f$ is at most
  $$\prod_{t=1}^T2\sqrt{\varepsilon_t(1-\varepsilon_t)}
  \le\exp\Bigl(-2\sum_{t=1}^T(\tfrac12-\varepsilon_t)^2\Bigr),$$
  and the fraction of points with normalized margin
  $y_if(x_i)/\|\alpha\|_1\le\rho$ is at most
  $2^T\prod_t\sqrt{\varepsilon_t^{1-\rho}(1-\varepsilon_t)^{1+\rho}}$. The
  empirical Rademacher complexity of the convex hull of a class equals that
  of the class, so the margin bound 107.10 applies to $f/\|\alpha\|_1$
  without dependence on $T$.

### Variational and exact inference

For an exponential family $p_\theta=\exp(\langle\theta,\phi\rangle-A(\theta))$
with respect to $\nu$, with open natural parameter space $\Omega$ and
affinely independent statistics, $\mathcal M$ is the set of means
$\mathbb E_p\phi$ over $\nu$-densities $p$ for which they exist, and
$A^*(\mu)=\sup_{\theta\in\Omega}\{\langle\mu,\theta\rangle-A(\theta)\}$. A
**junction tree** of a graph is a tree on its maximal cliques in which every
clique on the path between two cliques contains their intersection.

* **107.26. Variational representation of the cumulant function.**
  $\nabla A$ maps $\Omega$ onto $\mathcal M^\circ$; for
  $\mu\in\mathcal M^\circ$, $A^*(\mu)$ is the negative entropy of the unique
  member with mean $\mu$, and $A^*=+\infty$ off $\bar{\mathcal M}$. Moreover
  $A(\theta)=\sup_{\mu\in\mathcal M}\{\langle\theta,\mu\rangle-A^*(\mu)\}$,
  attained uniquely at $\mu=\mathbb E_\theta\phi$. For a finite discrete
  model $\max_x\langle\theta,\phi(x)\rangle
  =\max_{\mu\in\bar{\mathcal M}}\langle\theta,\mu\rangle
  =\lim_{\beta\to\infty}A(\beta\theta)/\beta$. Mathlib proves the
  one-parameter case of the gradient identity: the first two derivatives of
  the cumulant-generating function are the tilted mean and variance
  (`ProbabilityTheory.deriv_cgf`, `ProbabilityTheory.iteratedDeriv_two_cgf`);
  multiparameter families, $\mathcal M$, and the duality are missing.

* **107.27. Junction-tree exactness.** A graph has a junction tree if and
  only if it is triangulated. On a junction tree with finite state spaces,
  nonnegative clique and separator tables are the marginals of a joint
  probability law if and only if every table is normalized and, on each
  tree edge, both incident clique tables marginalize to its separator
  table. The joint law that is Markov with respect to the graph is unique
  and is the product of clique tables divided by the product of separator
  tables, with one separator factor per tree edge. A configuration with a
  zero separator factor has probability zero; the ratio is interpreted
  with $0/0=0$. The prescribed marginals need not determine a joint law
  outside the Markov class.

### Deep learning: architectures, approximation, and training

A one-hidden-layer network with $n$ units and activation $\phi$ is
$x\mapsto b_0+\sum_{k\le n}c_k\phi(\langle a_k,x\rangle+b_k)$; deeper networks
alternate affine maps and coordinatewise activations.

* **107.28. Barron's rate.** For the ReLU or a continuous sigmoidal
  activation there is $c$ such that, for all $d,n\ge1$, every probability
  measure $\mu$ on the closed unit ball of $\mathbb R^d$, and every
  continuous integrable $f:\mathbb R^d\to\mathbb R$ with
  $C_f=\int\|\omega\||\hat f(\omega)|\,d\omega<\infty$, some one-hidden-layer
  network with $n$ units and an output bias is within $cC_fn^{-1/2}$ of $f$
  in $L^2(\mu)$. The pointwise target is the continuous representative
  determined by Fourier inversion, including when $\mu$ is singular with
  respect to Lebesgue measure. Mathlib supplies the Fourier transform, and
  TauCeti specifies one-hidden-layer and deeper networks with their
  realizations; the approximation theorem and the probabilistic (Maurey)
  sampling argument are missing.

* **107.29. Deep networks and compositional classes.** Fix $q\ge0$,
  dimensions $d_0=d,d_1,\ldots,d_q$ and $d_{q+1}=1$, integers
  $1\le t_i\le d_i$, smoothness indices $\beta_i>0$, and $K>0$. Let
  $\mathcal G$ be the class of $f=g_q\circ\cdots\circ g_0$ with
  $g_i:[a_i,b_i]^{d_i}\to[a_{i+1},b_{i+1}]^{d_{i+1}}$, $[a_0,b_0]=[0,1]$,
  $|a_i|,|b_i|\le K$, such that each coordinate of $g_i$ depends on at most
  $t_i$ of its arguments and, as a function of those, lies in the Hölder
  ball of smoothness $\beta_i$ and radius $K$: on a domain
  $D\subset\mathbb R^r$ this ball consists of the $g$ whose partial
  derivatives of order $|\alpha|<\beta$ exist and satisfy
  $$\sum_{|\alpha|<\beta}\sup_D|\partial^\alpha g|
  +\sum_{|\alpha|=\lfloor\beta\rfloor}\sup_{x\ne y}
  \frac{|\partial^\alpha g(x)-\partial^\alpha g(y)|}
  {\|x-y\|_\infty^{\beta-\lfloor\beta\rfloor}}\le K,$$
  with $\lfloor\beta\rfloor$ the largest integer strictly smaller than
  $\beta$. Observe $n$ independent copies of $(X,Y)$ with
  $Y=f(X)+\varepsilon$, $\varepsilon$ standard normal and independent of
  $X$, and $X$ with a Lebesgue density on $[0,1]^d$ bounded above and below
  by positive constants; the risk of $\hat f$ is
  the nonnegative extended-real expectation $\mathbb E\int(\hat f-f)^2\,dP_X$,
  allowed to be infinite for arbitrary estimators. Put
  $\beta_i^*=\beta_i\prod_{j=i+1}^q\min(\beta_j,1)$ and
  $\phi_n=\max_{0\le i\le q}n^{-2\beta_i^*/(2\beta_i^*+t_i)}$. If
  $t_i\le\min(d_0,\ldots,d_{i-1})$ for every $i$, then for all sufficiently
  large $K$ there is $c>0$ such that every estimator has maximal risk over
  $\mathcal G$ at least $c\phi_n$. For every $K$ there are $C$ and, for each
  $n\ge2$, a class of sparse ReLU networks of depth of order $\log n$, with
  all weights and shifts in $[-1,1]$ and outputs bounded by $\max(K,1)$,
  such that every least-squares estimator over that class has maximal risk
  over $\mathcal G$ at most $C\phi_n(\log n)^3$; this upper bound does not
  use the density assumption on $X$ (Schmidt-Hieber).

* **107.30. Neural tangent kernel.** In the neural tangent
  parameterization a fully connected network of depth $L$ with widths
  $n_0=d,n_1,\ldots,n_L=1$ and activation $\sigma$ has $\alpha^{(0)}(x)=x$,
  $\tilde\alpha^{(\ell+1)}=n_\ell^{-1/2}W^{(\ell)}\alpha^{(\ell)}+\beta b^{(\ell)}$,
  $\alpha^{(\ell)}=\sigma(\tilde\alpha^{(\ell)})$ coordinatewise for
  $1\le\ell<L$, and output $f_\theta=\tilde\alpha^{(L)}$, with a fixed
  $\beta>0$ and all parameters initialized as independent standard normal
  variables. Let $\Theta_\theta(x,x')=\sum_p\partial_{\theta_p}f_\theta(x)
  \partial_{\theta_p}f_\theta(x')$, and train on inputs $x_1,\ldots,x_n$
  with targets $y$ by the gradient flow
  $\dot\theta_t=-\nabla_\theta(2n)^{-1}\sum_i(f_{\theta_t}(x_i)-y_i)^2$,
  with $f_t$ the vector of training outputs and $\Theta_t$ the $n\times n$
  kernel matrix at time $t$. Then $\dot f_t=-\Theta_t(f_t-y)/n$ at every
  width. If $\sigma$ is Lipschitz and twice differentiable with bounded
  second derivative and the hidden widths $n_1,\ldots,n_{L-1}$ tend to
  infinity one after the other, then $\Theta_0$ converges in probability to
  a deterministic positive semidefinite matrix $\Theta$, given by an
  explicit layer recursion, and $\sup_{0\le t\le T}\|\Theta_t-\Theta\|\to0$
  in probability for every $T>0$.

* **107.31. Ridgeless least squares.** For independent standard normal
  $x_i\in\mathbb R^p$, $y_i=x_i^\top\beta+\varepsilon_i$ with independent
  centered errors of variance $\sigma^2$, and $\hat\beta$ the
  minimum-norm least-squares estimator, the expected excess prediction risk
  $\mathbb E(x^\top\hat\beta-x^\top\beta)^2$ is $\sigma^2p/(n-p-1)$ for
  $n>p+1$ and $\|\beta\|^2(1-n/p)+\sigma^2n/(p-n-1)$ for $p>n+1$; if
  $p/n\to\gamma\ne1$ and $\|\beta\|^2\to r^2$, the limits are
  $\sigma^2\gamma/(1-\gamma)$ and $r^2(1-1/\gamma)+\sigma^2/(\gamma-1)$.
  TauCeti proves the Wishart law of a Gaussian Gram matrix and the
  inverse-Wishart mean $(n-p-1)^{-1}S$, which give the case $n>p+1$ by a
  short computation; the case $p>n+1$ needs the corresponding moments of the
  projection onto the row space, and neither the risk identities nor the
  limits are stated.

### Capacity, depth, and symmetry

* **107.35. Capacity of network classes.** For a fixed piecewise-polynomial
  activation there is $c$ such that sign classifiers of any architecture of
  depth $L$ with $P$ parameters have VC dimension at most
  $c(PL\log P+PL^2)$. For every class of VC dimension $v$ the $0$–$1$
  risks satisfy, with probability at least $1-\delta$,
  $\sup_f|R(f)-R_n(f)|\le c'\sqrt{(v+\log(1/\delta))/n}$ with an absolute
  constant $c'$. Hence for each depth $L$ there is $c_L$ such that, for
  $P\ge2$, the bound $c_L\sqrt{(P\log P+\log(1/\delta))/n}$ holds for these
  architectures. For bias-free networks on the
  unit ball with a $1$-Lipschitz positively homogeneous activation and
  weight matrices of Frobenius norm at most $C$, the Rademacher complexity
  of the real-valued class is at most $2^{L-1}C^L/\sqrt n$, independently
  of the widths. TauCeti's multilayer perceptron specifications, with their
  hidden-neuron permutation and scaling symmetries, are the only network
  layer; Mathlib's VC dimension is that of finite set families, and no
  capacity bound for network classes is stated.

* **107.36. Approximation rates of deep ReLU networks.** For $k\ge2$,
  $p\in[1,\infty]$, $s\in[0,1]$, $B>0$, and a piecewise-linear activation
  with a breakpoint, there is $c$ such that for each
  $\varepsilon\in(0,1/2)$ one architecture with at most
  $c\varepsilon^{-d/(k-s)}\log(1/\varepsilon)$ parameters approximates
  every $g$ with $\|g\|_{W^{k,p}((0,1)^d)}\le B$ within $\varepsilon$ in
  $W^{s,p}((0,1)^d)$ (Yarotsky for $p=\infty$, $s=0$).

* **107.37. Depth separation.** For the ReLU, logistic, or Heaviside
  activation there are $c,C>0$ such that for $d\ge C$ some probability
  measure on $\mathbb R^d$ and some function bounded by $2$, computed by a
  two-hidden-layer network of width at most $Cd^5$ and weights at most
  $Cd^C$, are at $L^2$ distance at least $c$ from every one-hidden-layer
  network of width at most $ce^{cd}$ (Eldan–Shamir). If
  $g\in C^2([0,1]^d)$ is not affine and $L\ge2$, there are
  $c,\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$
  every ReLU network with $L-1$ hidden layers and at most
  $c\varepsilon^{-1/(2(L-1))}$ neurons has uniform error at least
  $\varepsilon$ on $[0,1]^d$ (Yarotsky).

### Random initialization and implicit bias

* **107.39. Gaussian-process limit at initialization.** For a fully
  connected network with independent $N(0,C_b)$ biases and $N(0,C_W/N_\ell)$
  weights into layer $\ell+1$, and a continuous activation with
  $|\sigma(u)|\le a+b|u|$, at fixed depth and finitely many inputs the
  preactivation coordinates of each layer converge jointly in distribution,
  as the hidden widths tend to infinity, to independent centered Gaussian
  processes with covariance $K^{(1)}(x,x')=C_b+C_W\langle x,x'\rangle/d$ and
  $K^{(\ell+1)}(x,x')=C_b+C_W\mathbb E[\sigma(U)\sigma(U')]$, where
  $(U,U')$ is centered Gaussian with covariance $K^{(\ell)}$ on
  $\{x,x'\}$.

* **107.40. Implicit bias of gradient descent.** For
  $\frac12\|X\theta-y\|^2$, gradient descent with constant step
  $0<\eta<2/\lambda_{\max}(X^\top X)$ from $\theta_0$ converges to
  $X^+y+(I-X^+X)\theta_0$, the minimum-norm solution when $\theta_0=0$. For
  linearly separable data and the logistic loss there is $\eta_0>0$ such
  that gradient descent with any step in $(0,\eta_0)$ from any start has
  $\|\theta_t\|\to\infty$ and $\theta_t/\|\theta_t\|\to\hat\theta/\|\hat\theta\|$,
  with $\hat\theta$ the hard-margin solution (Soudry et al.). TauCeti
  constructs the Moore–Penrose inverse of a linear map between
  finite-dimensional inner product spaces from its singular system and
  characterizes it by the four Penrose equations, which supplies the limit
  $X^+y+(I-X^+X)\theta_0$; no library proves a convergence theorem for
  gradient descent, and the logistic implicit bias is absent.

### Networks and graph representation learning

In the **symmetric two-group stochastic block model** $n$ vertices are split
equally at random into two groups, and edges are independent with
probability $p$ within and $q$ between groups. A **graphon** is a symmetric
measurable $W:[0,1]^2\to[0,1]$; its model draws independent uniform $U_i$
and includes each edge $\{i,j\}$ independently with probability
$W(U_i,U_j)$.

* **107.41. Exact recovery.** For $p=a\log n/n$ and $q=b\log n/n$ with fixed
  $a,b>0$, recovery of the partition up to a global flip with probability
  tending to one is possible, and achievable in polynomial time, if and only
  if $(\sqrt a-\sqrt b)^2\ge2$; for $b=0$ and $a>0$ it is possible if and
  only if $a>2$.

* **107.42. Kesten–Stigum threshold.** For $p=a/n$, $q=b/n$ with fixed
  $a,b>0$, weak recovery (a labelling with overlap at least some
  $\varepsilon>0$ with probability tending to one) is possible if and only
  if $(a-b)^2>2(a+b)$, and efficiently so above the threshold. If
  $(a-b)^2<2(a+b)$, the model is mutually contiguous to
  $G(n,(a+b)/(2n))$, so no test distinguishes them consistently. No library
  defines the block model. Statlib defines contiguity of sequences of laws in
  several forms, among them the sequential one used here, of which mutual
  contiguity is the conjunction of the two directions; it proves only one
  equivalence and one implication between these forms, not Le Cam's first
  lemma, and no contiguity of graph laws is stated.

* **107.43. Aldous–Hoover theorem for graphs.** A random simple graph on the
  positive integers whose law is invariant under finite vertex permutations
  is a mixture of graphon models, and two graphons induce the same law if
  and only if they have almost everywhere equal pullbacks under suitable
  measure-preserving maps from a common atomless probability space. TauCeti
  proves the mixture representation for laws invariant under all
  permutations of $\mathbb N$, with a unique mixing measure on graphons
  modulo cut distance zero, and the equivalence of cut distance zero with
  equal sampling laws; missing are the reduction from finite to all
  permutations and the attained form of weak isomorphism, from cut distance
  zero to almost everywhere equal pullbacks (Borgs–Chayes–Lovász).

### Random graphs and spectral recovery

* **107.47. Phase transitions of the Erdős–Rényi graph.** For $p=c/n$ with
  fixed $c$: if $c<1$, with probability tending to one all components have
  at most $C\log n$ vertices; if $c>1$, the largest component satisfies
  $|C_1|/n\to\zeta_c$ in probability, with $\zeta_c\in(0,1)$ the positive
  root of $1-\zeta=e^{-c\zeta}$, and all other components have at most
  $C\log n$ vertices with probability tending to one. For
  $p=(\log n+x_n)/n$ the graph is connected with probability tending to one
  if $x_n\to\infty$, has isolated vertices with probability tending to one
  if $x_n\to-\infty$, and is connected with probability tending to
  $\exp(-e^{-x})$ if $x_n=x$. Mathlib defines the binomial random graph and
  its point probabilities only.

### Bandits and reinforcement learning

A **stochastic bandit** has $K$ arms with reward laws $\nu_k$; $\Delta_k$ is
the gap between the optimal mean and the mean of arm $k$, $\nu^\star$ the law
of an optimal arm, and the regret after $n$ plays is $n$ times the optimal
mean minus the expected total reward. The **Bellman optimality operator** of
a finite discounted model is
$(TQ)(s,a)=\mathbb E[R+\gamma\max_{a'}Q(S',a')\mid S=s,A=a]$.

* **107.49. Lai–Robbins lower bound.** In an exponential-family bandit
  $\nu_\theta(dx)=\exp(\theta x-b(\theta))\lambda(dx)$, with $\lambda$ not a
  point mass and $\theta$ in an open interval $\Theta$, a policy whose regret
  is $o(n^\alpha)$ for every $\alpha>0$ at every configuration in
  $\Theta^K$ satisfies, at every configuration,
  $$\liminf_{n\to\infty}\frac{\mathop{\mathrm{regret}}(n)}{\log n}
  \ge\sum_{k:\Delta_k>0}\frac{\Delta_k}{\mathop{\mathrm{kl}}(\nu_k,\nu^\star)}.$$
  Mathlib supplies the Ionescu–Tulcea law of the interaction and the
  divergence chain rule and data-processing inequality
  (`InformationTheory.klDiv_compProd_eq_add`,
  `InformationTheory.klDiv_map_le`), which are the change-of-measure steps.
  Statlib proves the single-arm form of the divergence decomposition: for
  independent identically distributed observations up to a stopping time,
  the divergence of the two laws of the observed segment is the expected
  number of observations times the divergence of one observation. It also
  proves Wald's identity and the Bretagnolle–Huber inequality. The bandit
  model, the decomposition of the divergence between the interaction laws of
  two configurations under one policy into expected numbers of plays times
  per-arm divergences, and the argument are missing.

* **107.50. Upper confidence bounds.** For rewards supported on $[0,1]$,
  UCB1, which plays each arm once and then an arm maximizing
  $\bar x_j+\sqrt{2\log t/n_j}$ after $t$ plays, has regret at most
  $8\sum_{k:\Delta_k>0}(\log n)/\Delta_k+(1+\pi^2/3)\sum_k\Delta_k$ for all
  $n\ge K$. Hoeffding's inequality is in Mathlib; the policy and the
  counting argument are missing.

* **107.51. Thompson sampling and the Gittins index.** For Bernoulli arms
  with means in $(0,1)$, a unique optimal arm, and independent uniform
  priors, Thompson sampling attains the Lai–Robbins constant:
  $\mathop{\mathrm{regret}}(n)/\log n\to
  \sum_{k:\Delta_k>0}\Delta_k/\mathop{\mathrm{kl}}(\nu_k,\nu^\star)$. For a
  Markov bandit with independent arms on countable state spaces, bounded
  rewards, and discount $\beta\in(0,1)$, always playing an arm of largest
  Gittins index
  $G_k(x)=\sup_{\tau\ge1}\mathbb E_x\sum_{t<\tau}\beta^tr_k(X^k_t)
  /\mathbb E_x\sum_{t<\tau}\beta^t$ maximizes the expected discounted
  reward. TauCeti constructs the path law of a homogeneous Markov chain;
  indices and policies are missing.

* **107.52. Adversarial bandits.** Against an oblivious sequence of loss
  vectors in $[0,1]^K$, $K\ge2$, Exp3 with the importance-weighted estimates
  $\hat\ell_t(i)=\ell_t(i)1_{\{I_t=i\}}/p_t(i)$, which are conditionally
  unbiased, and $\eta=\sqrt{2\log K/(TK)}$ has expected regret at most
  $\sqrt{2TK\log K}$ after $T$ rounds.

* **107.54. Convergence of $Q$-learning.** In a finite discounted model, let
  tabular $Q$-learning update the visited pair $(s_t,a_t)$ by
  $Q\leftarrow(1-\alpha_t)Q+\alpha_t(r_t+\gamma\max_{a'}Q(s_t',a'))$, where
  conditionally on the past and $(s_t,a_t)$ the next state has law
  $P(\cdot\mid s_t,a_t)$ and the bounded reward has the reward law of the
  pair, and the steps $\alpha_t(s,a)\in[0,1]$ are determined by the past
  and $(s_t,a_t)$, vanish off the visited pair, and satisfy almost surely
  $\sum_t\alpha_t(s,a)=\infty$ and $\sum_t\alpha_t(s,a)^2<\infty$ for every
  pair. Then $Q_t\to Q^\star$ almost surely. Mathlib's martingale
  convergence theorem and the Banach fixed-point theorem are ingredients; a
  stochastic-approximation theorem of Robbins–Siegmund type is missing.

### Optimal policies, planning, and sample complexity

* **107.58. Stationary optimal policies and linear programming.** In a
  finite discounted model, with $V^\star,Q^\star$ the suprema over all
  history-dependent randomized policies, some stationary deterministic
  policy attains both everywhere, and every policy greedy for $Q^\star$
  does. $V^\star$ is the componentwise smallest $V$ with
  $V(s)\ge r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V(s')$ for all $(s,a)$, and
  for an initial law $\mu$ of full support the unique minimizer of
  $\sum_s\mu(s)V(s)$ over this set. The occupancy measures
  $d^\pi_\mu(s,a)=(1-\gamma)\sum_t\gamma^tP_{\mu,\pi}(S_t=s,A_t=a)$ of
  stationary policies are exactly the nonnegative $d$ with
  $\sum_ad(s,a)=(1-\gamma)\mu(s)+\gamma\sum_{s',a'}P(s\mid s',a')d(s',a')$,
  $J(\pi)=(1-\gamma)^{-1}\sum d^\pi_\mu r$, and an optimal $d^\star$ for
  full-support $\mu$ yields the optimal policy
  $d^\star(s,a)/\sum_{a'}d^\star(s,a')$. Mathlib has the Banach fixed-point
  theorem, the Neumann series, and the cone form of Farkas' lemma
  (`ProperCone.hyperplane_separation`); the model, values, and the
  occupancy characterization are missing.

* **107.59. Sample complexity with a generative model.** In a finite
  discounted model with known rewards $r(s,a)\in[0,1]$, draw for each
  state-action pair $N$ independent next states from $P(\cdot\mid s,a)$, let
  $\hat P$ be the empirical transition law, and let hats denote quantities
  of the model with $\hat P$ in place of $P$. For every stationary policy
  $\pi$, $Q^\pi-\hat Q^\pi=\gamma(I-\gamma\hat P^\pi)^{-1}(P-\hat P)V^\pi$,
  with $\hat P^\pi$ the empirical state-action transition matrix under
  $\pi$; hence $\|Q^\pi-\hat Q^\pi\|_\infty\le\gamma(1-\gamma)^{-1}
  \|(P-\hat P)V^\pi\|_\infty$. There is an absolute constant $c$ such that,
  if $\varepsilon\le1$, $\delta\in(0,1)$, and
  $N\ge c\log(c|S||A|/\delta)/((1-\gamma)^3\varepsilon^2)$, then with
  probability at least $1-\delta$,
  $\|\hat Q^\star-Q^\star\|_\infty\le\varepsilon$. If
  $\varepsilon\le(1-\gamma)^{-1/2}$, the same condition on $N$ makes an
  optimal policy $\hat\pi$ of the empirical model satisfy
  $\|Q^{\hat\pi}-Q^\star\|_\infty\le\varepsilon$ with probability at least
  $1-\delta$. Conversely, there are absolute constants
  $\varepsilon_0,\delta_0\in(0,1)$ and $c'>0$ and a class of models such
  that, for $\varepsilon<\varepsilon_0$ and $\delta<\delta_0$, every
  procedure that on each model of the class outputs $\hat Q$ with
  $\|\hat Q-Q^\star\|_\infty\le\varepsilon$ with probability at least
  $1-\delta$ uses at least
  $c'|S||A|\log(c'/\delta)/((1-\gamma)^3\varepsilon^2)$ samples from the
  generative model. The identity is one step from Mathlib's Neumann
  series. The $(1-\gamma)^{-3}$ rate needs a Bernstein-type variance
  argument: TauCeti's Bernstein inequality for independent bounded summands
  gives the concentration of $(\hat P-P)V$ for each fixed $V$, but the
  bound on the total variance of the discounted returns and the passage to
  the data-dependent values $\hat V^\star$ are missing, and so is the lower
  bound.

* **107.60. Temporal differences with linear features.** For a fixed
  policy, let the states form an irreducible aperiodic chain on
  $\{1,\ldots,n\}$ with transition matrix $P$, stationary law $\varpi$,
  one-step costs $g(i,j)$, and value $V$, and let $\Phi$ be an $n\times K$
  feature matrix of full column rank with rows $\phi(i)^\top$. For
  $\lambda\in[0,1]$, TD($\lambda$) runs along one trajectory $(i_t)$ with
  $d_t=g(i_t,i_{t+1})+\gamma\phi(i_{t+1})^\top r_t-\phi(i_t)^\top r_t$,
  $z_t=\sum_{k\le t}(\gamma\lambda)^{t-k}\phi(i_k)$, and
  $r_{t+1}=r_t+\alpha_td_tz_t$. Let $\Pi$ be the orthogonal projection onto
  the range of $\Phi$ in the $\varpi$-weighted norm. If the steps are
  positive and deterministic with $\sum_t\alpha_t=\infty$ and
  $\sum_t\alpha_t^2<\infty$, then $r_t\to r^\star$ almost surely, where
  $\Phi r^\star$ is the unique fixed point of $\Pi T^{(\lambda)}$, with
  $T^{(\lambda)}=(1-\lambda)\sum_{m\ge0}\lambda^mT^{m+1}$ for $\lambda<1$,
  $T^{(1)}$ the constant map to $V$, and $T$ the policy Bellman operator.
  Moreover
  $$\|\Phi r^\star-V\|_\varpi\le\frac{1-\gamma\lambda}{1-\gamma}
  \|\Pi V-V\|_\varpi,$$
  and for $\lambda=1$ the limit is $\Pi V$.

* **107.61. Convergence of natural policy gradient.** For a finite
  discounted model with rewards in $[0,1]$ and the softmax policy
  $\pi_\theta(a\mid s)\propto e^{\theta_{s,a}}$, the natural policy gradient
  update is $\pi^{(t+1)}(a\mid s)\propto\pi^{(t)}(a\mid s)
  \exp(\eta A^{(t)}(s,a)/(1-\gamma))$, and from $\theta^{(0)}=0$ with any
  $\eta>0$,
  $$J^\star(\rho)-J(\pi^{(T)})\le\frac{\log|A|}{\eta T}
  +\frac1{(1-\gamma)^2T}\qquad(T\ge1).$$

### Minimax and linear bandits

* **107.62. Minimax regret of finite-armed bandits.** For $K\ge2$ and
  $n>K/(4\log(4/3))$, every possibly randomized strategy has regret at least
  $(\sqrt2-1)\sqrt{nK}/\sqrt{32\log(4/3)}$ on some instance with
  independent Bernoulli rewards, and UCB1 has regret at most
  $C\sqrt{Kn\log n}$ for all $n\ge\max(K,2)$ and all reward laws on
  $[0,1]$. Statlib's Bretagnolle–Huber inequality, which bounds the sum of
  the two error probabilities of any test below by $\frac12e^{-D(P\|Q)}$,
  and its tensorization of the divergence over products supply the
  two-point step of the lower bound; the bandit instances, the divergence
  decomposition under a policy, and the UCB1 bound are missing.

* **107.63. Self-normalized confidence and LinUCB.** Let $\varepsilon_t$ be
  real, $\mathcal F_t$-measurable, conditionally centered and
  $\sigma$-sub-Gaussian given $\mathcal F_{t-1}$, let $X_t\in\mathbb R^d$
  be $\mathcal F_{t-1}$-measurable, and let $V_t=V_0+\sum_{i\le t}X_iX_i^\top$
  with $V_0$ positive definite. With probability at least $1-\delta$,
  simultaneously for all $t\ge1$,
  $$\Bigl\|\sum_{i\le t}X_i\varepsilon_i\Bigr\|_{V_t^{-1}}^2
  \le2\sigma^2\log\frac{\det(V_t)^{1/2}\det(V_0)^{-1/2}}{\delta}.$$
  In a linear bandit the learner picks $x_t$ in a decision set
  $\mathcal D\subseteq\mathbb R^d$, observes
  $\langle\mu^\star,x_t\rangle+\eta_t$, and has regret
  $R_T=\sum_{t<T}(\max_{x\in\mathcal D}\langle\mu^\star,x\rangle
  -\langle\mu^\star,x_t\rangle)$; LinUCB forms the ridge estimate
  $\hat\mu_t$ with $\Sigma_t=\lambda I+\sum_{\tau<t}x_\tau x_\tau^\top$ and
  chooses $x_t$ maximizing
  $\langle\hat\mu_t,x\rangle+\sqrt{\beta_t}(x^\top\Sigma_t^{-1}x)^{1/2}$.
  If $|\langle\mu^\star,x\rangle|\le1$ and $\|x\|_2\le B$ on $\mathcal D$,
  $\|\mu^\star\|_2\le W$, and the noise satisfies the conditions above,
  LinUCB with
  $\lambda=\sigma^2/W^2$ and
  $\beta_t=\sigma^2(2+4d\log(1+tB^2W^2/(d\sigma^2))+8\log(4/\delta))$ has,
  with probability at least $1-\delta$ and for all $T$,
  $R_T\le c\max\{\sigma,BW\}\sqrt T(d\log(1+TB^2W^2/(d\sigma^2))+\log(4/\delta))$
  with an absolute constant $c$, for $\sigma,B,W>0$ and $0<\delta<1$.
  The effective scale $\max\{\sigma,BW\}$ includes initial exploration.
  Conversely, there is a distribution over
  instances $\mu^\star$, with rewards in $[-1,1]$ and $\sigma\le1$, such that
  every algorithm has $\mathbb ER_T\ge d\sqrt T/2500$ for all
  $T\ge\max\{256,d^2/16\}$, the expectation including the draw of
  $\mu^\star$. Mathlib proves the fixed-horizon scalar
  Azuma–Hoeffding bound
  (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`), and
  TauCeti derives the Azuma–Hoeffding inequality for bounded martingale
  differences from a conditional Hoeffding lemma and extends Doob's maximal
  inequality to finite sets of times and to right-continuous submartingales
  up to a fixed horizon. The method of mixtures and a time-uniform maximal
  (Ville) inequality are missing.

### Privacy, fairness, and distribution shift

* **107.65. Composition.** The adaptive composition of $k$ mechanisms that
  are $(\varepsilon_i,\delta_i)$-differentially private is
  $(\sum\varepsilon_i,\sum\delta_i)$-differentially private. If each is
  $(\varepsilon,\delta)$-private, then for every $\delta'\in(0,1)$ the
  composition is $(\varepsilon',k\delta+\delta')$-private with
  $\varepsilon'=\sqrt{2k\log(1/\delta')}\,\varepsilon+k\varepsilon(e^\varepsilon-1)$.
  The advanced bound would use the Azuma–Hoeffding inequality, which Mathlib
  has in conditional sub-Gaussian form and TauCeti for bounded martingale
  differences; no privacy notion is defined.

* **107.66. Private mean estimation.** For $n$ independent observations
  from an unknown law on $[-1,1]$, the mean as target, squared error, and
  $0<\varepsilon\le1$, the minimax risk over estimators based on
  noninteractive $\varepsilon$-locally private releases is of order
  $\min\{1,1/(n\varepsilon^2)\}$, and over $\varepsilon$-differentially
  private estimators of order $\min\{1,n^{-1}+(n\varepsilon)^{-2}\}$, up to
  absolute constants; the latter upper bound is attained by the clipped
  Laplace-noised sample mean. TauCeti defines the Laplace law, and Statlib
  supplies ingredients of the two-point and Fano methods (the
  Bretagnolle–Huber inequality, tensorization of the divergence, and mutual
  information); the mechanisms, the contraction 107.75, and the two
  lower-bound methods themselves are missing.

### Threshold queries and local contraction

A release kernel $Q$ is **$\varepsilon$-locally private** if
$Q(B\mid x)\le e^\varepsilon Q(B\mid x')$ for all measurable $B$ and all
inputs $x,x'$; for an input law $P$ put $M_P=\int Q(\cdot\mid x)\,dP(x)$.

* **107.74. Sparse vector technique.** For an adaptive stream of queries of
  sensitivity at most $1$ and a public threshold $T$, AboveThreshold draws
  $\hat T=T+\mathop{\mathrm{Lap}}(2/\varepsilon)$ and independent noises
  $\nu_i\sim\mathop{\mathrm{Lap}}(4/\varepsilon)$, reports "below" while
  $f_i(D)+\nu_i<\hat T$, and halts with "above" at the first exceedance. It
  is $\varepsilon$-differentially private whatever the number of queries. If
  among the first $k$ queries only the last can satisfy $f_i(D)\ge T-\alpha$,
  then with probability at least $1-\beta$ it does not halt before query
  $k$, every "above" has $f_i(D)\ge T-\alpha$, and every "below" has
  $f_i(D)\le T+\alpha$, where $\alpha=8(\log k+\log(2/\beta))/\varepsilon$.
  TauCeti supplies the Laplace law and its distribution function.

* **107.75. Contraction under local privacy.** If $Q$ is
  $\varepsilon$-locally private, then for all input laws $P_1,P_2$,
  $$D(M_{P_1}\|M_{P_2})+D(M_{P_2}\|M_{P_1})
  \le4(e^\varepsilon-1)^2\|P_1-P_2\|_{\mathrm{TV}}^2,$$
  and for $n$ individuals with independent inputs, released through
  $\varepsilon$-locally private kernels that may depend on earlier releases,
  the same holds for the joint release laws with an extra factor $n$. The
  tensorization step follows from Mathlib's divergence chain rule once the
  single-release bound is known; TauCeti's Pinsker inequality bounds total
  variation by divergence, the opposite direction. Statlib's data-processing
  inequalities for total variation under a Markov kernel and for mutual
  information under kernels acting on each component give contraction
  without the factor $(e^\varepsilon-1)^2$. The reverse bound under a
  likelihood-ratio constraint is missing.

## 108. Geometry of data: manifolds, topology, optimal transport, and kernels

Mathlib supplies the unweighted graph Laplacian with its quadratic form and
component count, the spectral theorem and Rayleigh quotients, Gram matrices,
Hausdorff and Gromov–Hausdorff distances, abstract simplicial complexes,
reproducing-kernel Hilbert spaces with Moore's theorem, the real central limit
theorem with the Cramér–Wold device, a Banach-space strong law, Hoeffding's
inequality and Prokhorov's theorem. TauCeti adds Fréchet barycenters on metric
spaces with strong consistency and CAT(0) uniqueness, Ky Fan, Courant–Fischer
and orthogonal Procrustes principles, simplicial chain complexes with
Euler–Poincaré identities and their identification with singular homology,
Riemannian exponential maps, covering numbers of bounded sets in
finite-dimensional normed spaces, and on the transport side Wasserstein
barycenters (existence, Euclidean uniqueness, consistency of empirical
barycenters), the one-dimensional quantile isometry, the Gaussian Bures
formula with the fixed-point characterization of Gaussian barycenters,
Gromov–Wasserstein distances with the metric space of weak-isomorphism
classes, entropic duality with Sinkhorn half-steps, nonnegativity and
definiteness of the Sinkhorn divergence, the comparison of Wasserstein and
weak convergence, the Wasserstein tangent space, kernel mean embeddings,
universal kernels and Bochner's theorem. Statlib contributes only integral
forms of the total variation distance. The principal omissions
are spectral graph inequalities, intrinsic and extrinsic central limit
theorems on manifolds, the whole of persistent homology (persistence modules,
diagrams, stability and topological inference), every statistical rate of
optimal transport, the barycenter calculus in the tangent space, and the
statistical theory of kernel discrepancies: limits of MMD and HSIC
statistics, characteristic-kernel criteria, metrization of weak convergence,
kernel Stein discrepancies and random features.

Sources: [mathematical synopsis](SYNOPSIS108.md); [combined coverage inventory](STRUCTURE108.md).

Graphs are finite, undirected, without loops, with positive edge weights;
$D$ is the diagonal degree matrix and the **normalized Laplacian** is
$\mathcal L=I-D^{-1/2}AD^{-1/2}$, with eigenvalues
$0=\lambda_0<\lambda_1\le\cdots\le\lambda_{n-1}\le2$ for a connected graph.
On a metric space the **Fréchet function** of a probability $Q$ is
$F(p)=\int d(p,x)^2\,Q(dx)$, and a **Fréchet mean** is a minimizer of $F$.
$d_H$ is Hausdorff distance and $d_{GH}$ Gromov–Hausdorff distance. The
**reach** of a closed set is the largest radius at which the distance function
has a unique nearest point throughout the open tubular neighborhood; the
**offset** of $P$ at radius $r$ is $P^r=\{x:d(x,P)\le r\}$.

For $p\ge1$, $W_p$ is the $p$-Wasserstein distance on the space
$\mathcal P_p$ of Borel probabilities with finite $p$th moment, and
$\Pi(\mu,\nu)$ is the set of couplings. For a probability $\mu$ on
$\mathbb R^d$, $\mu_n$ denotes the empirical measure of $n$ independent
observations of law $\mu$. The **Brenier map** from an absolutely continuous
$\mu\in\mathcal P_2(\mathbb R^d)$ to $\nu\in\mathcal P_2(\mathbb R^d)$ is the
optimal map $\nabla\varphi$, $\varphi$ convex. Kernels $k$ are bounded,
measurable and positive semidefinite, with reproducing-kernel Hilbert space
$\mathcal H$; the **kernel mean embedding** is
$\Phi(\mu)=\int k(x,\cdot)\,\mu(dx)$, the **maximum mean discrepancy** is
$\mathop{\mathrm{MMD}}(\mu,\nu)=\|\Phi(\mu)-\Phi(\nu)\|_{\mathcal H}$, and $k$
is **characteristic** when $\Phi$ is injective on Borel probabilities.

### Manifold learning, geometric statistics, and shape

Chung's **Cheeger constant** is
$$h(G)=\min_{\varnothing\ne S\subsetneq V(G)}
\frac{|\partial S|}{\min(\mathop{\mathrm{vol}}S,\mathop{\mathrm{vol}}S^c)},$$
where $\mathop{\mathrm{vol}}S$ is the sum of the weighted degrees in $S$ and
$|\partial S|$ the total weight of edges with one end in $S$.

* **108.1. Cheeger inequality for the normalized Laplacian.** For a finite
  connected weighted graph with at least two vertices,
  $$\frac{\lambda_1}2\le h(G)\le\sqrt{2\lambda_1},$$
  and the sharper lower bound $\lambda_1\ge1-\sqrt{1-h(G)^2}$ holds as well.
  Mathlib has only the unweighted Laplacian $D-A$ and the Rayleigh-quotient
  characterization of extreme eigenvalues; no library defines the
  normalized Laplacian, conductance or Cheeger constant, and the sweep-cut
  argument for the upper bound is absent.

* **108.4. Geodesic approximation.** Let $M\subset\mathbb R^D$ be a
  compact connected smooth submanifold of positive reach, and let a noiseless
  sample be a $\delta_n$-net of $M$ in its intrinsic metric $d_M$. Join pairs
  of sample points at Euclidean distance at most $\varepsilon_n$, with edges
  weighted by Euclidean length, and let $d_{G_n}$ be the shortest-path
  distance. If $\varepsilon_n\to0$ and $\delta_n/\varepsilon_n\to0$, then
  $\max|d_{G_n}(x,y)-d_M(x,y)|\to0$ over pairs of sample points. If
  $\varphi:M\to\Omega$ is an isometry onto a convex domain
  $\Omega\subset\mathbb R^d$, then $d_M(x,y)=\|\varphi(x)-\varphi(y)\|$, and
  classical multidimensional scaling of the squared intrinsic distances of a
  finite sample returns the points $\varphi(x_i)$ up to a Euclidean isometry.
  Mathlib has Riemannian manifolds with their path-length distance, but
  submanifolds of positive reach, graph geodesics on samples, and the
  comparison theorem are absent from all three libraries.

* **108.5. Fréchet means.** In a complete
  Hadamard space every probability with finite second moment has a unique
  Fréchet mean. Let $X_1,X_2,\ldots$ be independent with law $Q$ on a
  $d$-dimensional Riemannian manifold with geodesic distance $\rho$, let $Q$
  have a unique Fréchet mean $m$, and let $\hat m_n$ be a measurable selection
  of sample Fréchet means with $\hat m_n\to m$ almost surely. Suppose $Q$ is
  supported in the domain $U$ of a chart $\phi:U\to\mathbb R^d$; put
  $h(x,y)=\rho(\phi^{-1}x,\phi^{-1}y)^2$ and $\tilde X=\phi(X_1)$, and write
  $D$ for derivatives in $y$. Assume that $y\mapsto h(x,y)$ is $C^2$ near
  $\phi(m)$ for every $x$, that $\mathbb E\|Dh(\tilde X,\phi(m))\|^2<\infty$,
  that $\mathbb E\sup_{\|u-v\|\le\varepsilon}
  \|D^2h(\tilde X,u)-D^2h(\tilde X,v)\|\to0$ as $\varepsilon\to0$, and that
  $\Lambda=\mathbb E\,D^2h(\tilde X,\phi(m))$ is nonsingular. Then
  $$\sqrt n\,\bigl(\phi(\hat m_n)-\phi(m)\bigr)\Rightarrow
  N(0,\Lambda^{-1}\Sigma\Lambda^{-1}),\qquad
  \Sigma=\mathop{\mathrm{Cov}}Dh(\tilde X,\phi(m)).$$
  TauCeti proves uniqueness of quadratic barycenters in CAT(0) metric spaces
  and existence, with almost-sure convergence of empirical barycenters, in
  proper CAT(0) spaces. Missing are existence in complete Hadamard spaces that
  are not proper, and the central limit theorem, which needs $M$-estimation
  and a multivariate delta method in a chart.

* **108.7. Hausdorff estimation of a submanifold.** Let $M\subset\mathbb R^D$
  be a compact smooth $d$-dimensional submanifold without boundary, and let
  $X_1,\ldots,X_n$ be independent with a law on $M$ whose density with respect
  to volume is bounded below by a positive constant. Then
  $d_H(\{X_1,\ldots,X_n\},M)=O_P((\log n/n)^{1/d})$. In the
  perpendicular-noise model (compact $d$-dimensional submanifolds without
  boundary, in a fixed compact set, with reach at least $\kappa>0$; each
  observation a uniform point of $M$ displaced uniformly in its normal ball of
  fixed radius $0<\sigma<\kappa$), the minimax risk
  $R_n=\inf_{\hat M}\sup_M\mathbb E\,d_H(\hat M,M)$ satisfies, for constants
  $0<c\le C$ and all large $n$,
  $$cn^{-2/(d+2)}\le R_n\le C(\log n/n)^{2/(d+2)}.$$
  Mathlib has the Hausdorff distance; volume measures of submanifolds,
  covering estimates on manifolds, reach, and any minimax framework are
  absent.

### Spectral coordinates and extrinsic statistics

* **108.8. Classical multidimensional scaling.** Let $D^{(2)}$ be a symmetric
  $n\times n$ matrix with zero diagonal, put $J=I-11^\top/n$ and
  $B=-JD^{(2)}J/2$. Then $D^{(2)}$ consists of squared Euclidean distances
  between some $n$ points if and only if $B$ is positive semidefinite. If
  $B=U\Lambda U^\top\ge0$, the rows of $U\Lambda^{1/2}$ are centered
  coordinates realizing these distances, unique up to a Euclidean isometry,
  and keeping the $k$ largest positive eigenvalues gives the best
  rank-at-most-$k$ positive semidefinite approximation to $B$ in Frobenius
  norm. Mathlib proves that Gram matrices are positive semidefinite and has the
  spectral theorem; TauCeti proves Eckart–Young in operator norm. The statement
  follows by a short argument (double centring identifies $B$ with the Gram
  matrix of centered points; a positive semidefinite $B$ factors through its
  spectral decomposition), but neither the Schoenberg criterion nor the
  Frobenius best approximation within positive semidefinite matrices is
  stated.

Let $j:M\to\mathbb R^D$ be an embedding with closed image. An **extrinsic
mean** of a random point $X$ of $M$ minimizes $\mathbb E\|j(X)-j(m)\|^2$ over
$m\in M$.

* **108.10. Extrinsic projection mean.** Let $X_1,X_2,\ldots$ be independent
  copies of $X$ with $j(X)\in L^2$, and put $\mu=\mathbb E j(X)$. The
  extrinsic means are the nearest points of $j(M)$ to $\mu$. If this
  nearest-point projection $P$ is single-valued and continuously
  differentiable near $\mu$, then
  $$\sqrt n\Bigl(P\bigl(n^{-1}\textstyle\sum_i j(X_i)\bigr)-P(\mu)\Bigr)
  \Rightarrow N(0,DP_\mu\Sigma DP_\mu^\top),\qquad
  \Sigma=\mathop{\mathrm{Cov}}(j(X)),$$
  and the limit is supported on the tangent space at $P(\mu)$. Mathlib's
  real central limit theorem with its Cramér–Wold theorem gives the
  multivariate limit of the sample mean; missing are the delta method, the
  nearest-point projection onto an embedded manifold, and the statement.

### Fréchet means and Procrustes analysis

* **108.13. Uniqueness of Fréchet means in small balls.** Let $M$ be a
  complete Riemannian manifold with sectional curvature at most $\Delta$ and
  injectivity radius $\mathop{\mathrm{inj}}(M)$, and put
  $r^*=\frac12\min\{\mathop{\mathrm{inj}}(M),\pi/\sqrt\Delta\}$, read as
  $\frac12\mathop{\mathrm{inj}}(M)$ when $\Delta\le0$. If the support of a
  probability $Q$ lies in an open geodesic ball $B(o,\rho)$ with $\rho<r^*$,
  the Fréchet mean is unique and lies in $B(o,\rho)$. TauCeti has the
  Riemannian exponential map, Hopf–Rinow and sectional curvature, and proves
  barycenter uniqueness in CAT(0) metric spaces; injectivity radius,
  comparison geometry under an upper curvature bound, convexity of $d^2$ in
  small balls, and the theorem are absent, and no Riemannian manifold is shown
  to be CAT(0).

* **108.15. Barycentric equation.** Let $M$ be a complete Riemannian manifold
  and $Q$ a probability with finite second moment. At a point $p$ whose cut
  locus has $Q$-measure zero, the Fréchet function is differentiable with
  $$\nabla F(p)=-2\int\mathop{\mathrm{Log}}_p(x)\,Q(dx),$$
  so a Fréchet mean at such a point satisfies
  $\int\mathop{\mathrm{Log}}_p(x)\,Q(dx)=0$. TauCeti's exponential map is a
  local diffeomorphism at the origin, but the cut locus, the Riemannian
  logarithm on its complement, and the differentiability of squared distance
  are absent.

### Persistent homology and computational topology

A **persistence module** over $\mathbb R$ with coefficients in a field assigns
a vector space $V_t$ to each $t$ and a linear map $V_s\to V_t$ to each
$s\le t$, compatibly with composition. It is **pointwise finite-dimensional**
when each $V_t$ is finite-dimensional, and **$q$-tame** when each map
$V_s\to V_t$, $s<t$, has finite rank. An **interval module** has
one-dimensional spaces on an interval with identity maps inside it and zero
elsewhere. For a tame function $f$ (finitely many homological critical values
of its sublevel sets $X_a=f^{-1}(-\infty,a]$, all $H_p(X_a)$
finite-dimensional) on a triangulable space, $\mathop{\mathrm{Dgm}}_p(f)$ is
the $p$-th persistence diagram of the sublevel filtration, together with the
diagonal at infinite multiplicity. The **bottleneck distance** $d_B$ is the
infimum over bijections of diagrams of the supremum of $\ell^\infty$ distances
of matched points. An **$\varepsilon$-interleaving** of modules $U,V$ is a pair
of families $U_t\to V_{t+\varepsilon}$, $V_t\to U_{t+\varepsilon}$ commuting
with structure maps whose composites are the structure maps
$U_t\to U_{t+2\varepsilon}$, $V_t\to V_{t+2\varepsilon}$; the
**interleaving distance** is the infimum of such $\varepsilon$.

* **108.18. Interval decomposition.** A pointwise finite-dimensional
  persistence module over a field decomposes as a direct sum of interval
  modules, and the multiset of intervals is unique. TauCeti proves Gabriel's
  theorem, whose type $A_n$ case is the natural input over a finite totally
  ordered index set; no library defines persistence or interval modules,
  identifies the indecomposables, or treats the index set $\mathbb R$
  (Crawley-Boevey's theorem).

* **108.19. Bottleneck stability.** For tame functions $f,g$ on a
  triangulable space and every $p\ge0$,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le\|f-g\|_\infty.$$
  Persistence diagrams, matchings, and the bottleneck distance are absent from
  all three libraries.

* **108.20. Isometry theorem.** For $q$-tame persistence modules the
  interleaving distance equals the bottleneck distance between their
  persistence diagrams. Absent from all three libraries.

For a finite set $S$ in a metric space, the **Čech complex** at radius $r$ is
the nerve of the closed $r$-balls centered at $S$, and the **Vietoris–Rips
complex** at parameter $r$ consists of the subsets of $S$ of diameter at most
$2r$.

* **108.21. Čech, Rips, and the nerve.** In Euclidean space
  $\mathrm{Cech}(r)\subseteq\mathrm{Rips}(r)\subseteq\mathrm{Cech}(\sqrt2\,r)$.
  With the Rips parameter redefined as the maximum edge length, in any metric
  space $\mathrm{Rips}_r\subseteq\mathrm{Cech}_r\subseteq\mathrm{Rips}_{2r}$.
  The nerve of a finite collection of closed convex sets in Euclidean space has
  the homotopy type of their union. TauCeti proves that the Čech–singular
  total complex of an open cover is quasi-isomorphic to the singular chains,
  the homological form of the nerve lemma for open covers with acyclic
  intersections; the nerve of a cover as a simplicial complex, the homotopy
  nerve theorem for closed convex sets, and the Čech and Rips complexes are
  absent.

* **108.22. Homology from a sample.** Let $M\subset\mathbb R^D$ be a compact
  smooth $d$-dimensional submanifold without boundary with reach $\tau>0$, and
  let $P\subset M$ be finite and nonempty with
  $d_H(P,M)=\varepsilon<\sqrt{3/20}\,\tau$. Then for
  every $r\in(2\varepsilon,\sqrt{3/5}\,\tau)$ the offset $P^r$ deformation
  retracts onto $M$, so the Čech complex of radius $r$ has the homotopy type of
  $M$. This radius interval is asserted for noiseless samples on $M$;
  Hausdorff closeness of an off-manifold cloud alone does not suffice.
  If $X_1,\ldots,X_n$ are independent with a law on $M$ whose density
  with respect to volume is bounded below by a positive constant, then
  $d_H(\{X_1,\ldots,X_n\},M)\le\varepsilon$ with probability at least
  $1-\delta$ whenever
  $n\ge C\varepsilon^{-d}(\log(1/\varepsilon)+\log(1/\delta))$, for
  $0<\varepsilon<\varepsilon_0$ and $0<\delta<1$, with $C,\varepsilon_0$
  depending only on $M$ and the density bound. Reach, the deformation
  retraction of offsets, and the sampling bound are absent from all three
  libraries.

* **108.23. Central limit theorem for landscapes.** Realize a persistence
  landscape as a random element $\Lambda$ of $L^p(\mathbb N\times\mathbb R)$,
  with counting and Lebesgue measure. For independent copies of $\Lambda$, if
  $1\le p<\infty$ and $\mathbb E\|\Lambda\|_p<\infty$, their mean converges
  almost surely in $L^p$ to $\mathbb E\Lambda$. If $2\le p<\infty$ and
  $\mathbb E\|\Lambda\|_p^2<\infty$, the centered mean times $\sqrt n$
  converges in distribution to a centered Gaussian random element of $L^p$
  with the covariance of $\Lambda$. Mathlib's strong law for Banach-space
  valued variables gives the first statement once landscapes are defined;
  landscapes are not defined, and no central limit theorem in $L^p$,
  $p\ge2$, is available.

For a probability $\mu$ on $\mathbb R^D$ and $u\in(0,1]$ put
$\delta_{\mu,u}(x)=\inf\{r\ge0:\mu(\overline B(x,r))\ge u\}$; for a mass
$m\in(0,1]$ the **distance to the measure** is given by
$d_{\mu,m}(x)^2=m^{-1}\int_0^m\delta_{\mu,u}(x)^2\,du$.

* **108.24. Stability of the distance to a measure.** For probabilities on
  $\mathbb R^D$ with finite second moment,
  $\|d_{\mu,m}-d_{\nu,m}\|_\infty\le m^{-1/2}W_2(\mu,\nu)$. TauCeti has
  $W_2$; the distance to a measure and its stability are absent.

### Simplicial homology and the persistence algorithm

A **simplexwise filtration** orders the simplices of a finite complex as
$\sigma_1,\dots,\sigma_m$ so that every initial segment is a subcomplex. Its
boundary matrix $D$ over $\mathbb Z/2$ has $D_{ij}=1$ exactly when $\sigma_i$
is a codimension-one face of $\sigma_j$. For a nonzero column $j$,
$\mathop{\mathrm{low}}(j)$ is its largest row index with a nonzero entry. A
matrix is **reduced** when distinct nonzero columns have distinct lows; adding
columns to later columns gives $R=DV$ with $R$ reduced and $V$ invertible
upper triangular. $D^i_j$ is the submatrix of rows $i,\dots,m$ and columns
$1,\dots,j$. A $p$-simplex is **positive** if adding it raises $\beta_p$ and
**negative** if it lowers $\beta_{p-1}$.

* **108.32. Persistence pairing by matrix reduction.** For every such
  reduction, $\mathop{\mathrm{low}}_R(j)=i$ exactly when
  $$\mathop{\mathrm{rank}}D^i_j-\mathop{\mathrm{rank}}D^{i+1}_j
  +\mathop{\mathrm{rank}}D^{i+1}_{j-1}-\mathop{\mathrm{rank}}D^i_{j-1}=1,$$
  so the pairing does not depend on the reduction. If
  $\mathop{\mathrm{low}}_R(j)=i$, then $\sigma_i$ is a positive $p$-simplex,
  $\sigma_j$ a negative $(p+1)$-simplex, and $[i,j)$ a degree-$p$ bar; if
  column $j$ of $R$ is zero and $j$ is the low of no column, then $[j,\infty)$
  is an essential bar of degree $\dim\sigma_j$. For a monotone function $f$ on
  simplices ordered with $f(\sigma_1)\le\cdots\le f(\sigma_m)$, the bars of
  the sublevel filtration are the intervals $[f(\sigma_i),f(\sigma_j))$ and
  $[f(\sigma_j),\infty)$ so obtained, those of length zero discarded. The same
  holds over any field with signed boundary matrices. TauCeti has the ordered
  simplicial chain complex with $\partial\partial=0$ and identifies its
  homology with the singular homology of the realization; filtrations,
  boundary matrix reduction, and the pairing lemma are absent.

* **108.34. Sublevel persistence of a Morse function.** Let $f$ be a Morse
  function with distinct critical values on a closed smooth manifold $M$, with
  field coefficients. The homotopy type of $M_{\le a}=f^{-1}(-\infty,a]$
  changes only at critical values, and passing an index-$q$ critical value
  attaches a $q$-cell, so either a degree-$q$ bar is born or a
  degree-$(q-1)$ bar dies there. Every finite endpoint of the diagram is a
  critical value, each critical point is an endpoint of exactly one bar, and
  with $c_q$ the number of index-$q$ critical points,
  $$c_q=\#\{\text{degree-}q\text{ bars}\}
  +\#\{\text{finite degree-}(q-1)\text{ bars}\},$$
  with exactly $\beta_q(M)$ infinite degree-$q$ bars. TauCeti proves the
  Morse–Palais lemma and defines the Morse index; cell attachment at critical
  values and sublevel persistence are absent.

### Stability and inference for geometric filtrations

For persistence diagrams $X,Y$ and $1\le q<\infty$, the **$q$-Wasserstein
distance** is
$W_q(X,Y)=\inf_\eta(\sum_{x\in X}\|x-\eta(x)\|_\infty^q)^{1/q}$ over
bijections $\eta$ with the diagonal available. A triangulable compact metric
space has **polynomially growing triangulations** if triangulations of mesh at
most $r$ with at most $cr^{-j}$ simplices exist for small $r$.

* **108.35. Wasserstein stability.** Write $D_p^{\mathrm{fin}}(f)$ for the
  finite-death part of the diagram. For tame Lipschitz functions $f,g$ on
  such a space $X$ in a fixed degree $p\ge0$, choose $k\ge1$ with
  $k>j$. For every finite $q\ge k$
  there is $C$ depending on the space, $k,q$, and the Lipschitz constants
  such that, with $\delta=\|f-g\|_\infty>0$,
  $$W_q\bigl(D_p^{\mathrm{fin}}(f),D_p^{\mathrm{fin}}(g)\bigr)
  \le C\delta^{1-k/q}.$$
  The essential bars, whose number is $\beta_p(X)$ in each diagram,
  admit a matching with birth differences at most $\delta$. Consequently
  the full diagrams satisfy
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le C\delta^{1-k/q}+\beta_p(X)^{1/q}\delta.$$
  When $\delta=0$ both distances are zero. For
  monotone functions on the simplices of a finite complex $K$, meaning
  $f(\tau)\le f(\sigma)$ whenever $\tau$ is a face of $\sigma$,
  $$W_q\bigl(\mathop{\mathrm{Dgm}}_p(f),\mathop{\mathrm{Dgm}}_p(g)\bigr)
  \le\Bigl(\sum_{\sigma\in K}|f(\sigma)-g(\sigma)|^q\Bigr)^{1/q}.$$

  Absent from all three libraries.

* **108.36. Gromov–Hausdorff stability of Rips persistence.** For totally
  bounded metric spaces $X,Y$, the homology of their Rips filtrations is
  $q$-tame, and in the diameter-$2r$ parameter, in every degree,
  $$d_B\bigl(\mathop{\mathrm{Dgm}}\mathrm{Rips}(X),
  \mathop{\mathrm{Dgm}}\mathrm{Rips}(Y)\bigr)\le d_{GH}(X,Y);$$
  in the maximum-edge parameter the bound is $2d_{GH}(X,Y)$. For finite
  subsets of one metric space, the Rips and ambient Čech diagrams are within
  their Hausdorff distance, and the intrinsic Čech diagrams of finite metric
  spaces are within $2d_{GH}$. Mathlib defines $d_{GH}$ and bounds it by the
  Hausdorff distance of isometric embeddings, but not its description by
  distortion of correspondences; Rips filtrations, $q$-tameness, and the
  stability theorem are absent.

Let $K\subset\mathbb R^D$ be compact with distance function $d_K$. A point
$x\notin K$ is **critical** for $d_K$ if it lies in the convex hull of its
nearest points in $K$; the **weak feature size** $\mathrm{wfs}(K)$ is the
infimum of the positive critical values of $d_K$.

* **108.37. Homology inference with positive weak feature size.** Let $P$ be
  finite with $d_H(K,P)=\varepsilon<\mathrm{wfs}(K)/4$. If $\varepsilon<i$
  and $i+2\varepsilon\le j<\mathrm{wfs}(K)-\varepsilon$, the image of
  $H_*(P^i)\to H_*(P^j)$ is isomorphic to $H_*(K^r)$ for every
  $r\in(0,\mathrm{wfs}(K))$, and the same holds for the Čech complexes of radii
  $i$ and $j$. If instead $d_H(K,P)<\varepsilon$ for some
  $\varepsilon<\mathrm{wfs}(K)/9$ and
  $2\varepsilon\le\alpha\le(\mathrm{wfs}(K)-\varepsilon)/4$, the image of
  $H_*(\mathrm{Rips}(\alpha/2))\to H_*(\mathrm{Rips}(2\alpha))$ is isomorphic
  to $H_*(K^r)$, with the diameter-$2r$ Rips parameter. Critical points of
  distance functions, weak feature size, and the deformation retraction of
  offsets across noncritical intervals are absent from all three libraries.

### Optimal transport and Wasserstein statistics

* **108.40. Empirical Wasserstein bounds.** Let $p\ge1$ and let
  $A\subset\mathbb R^d$ be bounded. There is $C$ depending only on $p$, $d$,
  $A$ such that for every probability $\mu$ supported in $A$ and every $n\ge1$,
  $$\mathbb E W_p^p(\mu_n,\mu)\le C
  \begin{cases}n^{-1/2},&p>d/2,\\
  n^{-1/2}\log(1+n),&p=d/2,\\
  n^{-p/d},&p<d/2.
  \end{cases}$$
  More generally, for $q>p$ with $M_q(\mu)=\int\|x\|^q\,\mu(dx)<\infty$, and
  $q\ne2p$ if $p\ge d/2$, $q\ne d/(d-p)$ if $p<d/2$, the same bound holds with
  $C$ replaced by $CM_q(\mu)^{p/q}$, $C$ depending only on $p,d,q$, and with
  $n^{-(q-p)/q}$ added inside each case. TauCeti proves almost-sure
  convergence $W_p(\mu_n,\mu)\to0$ on separable spaces; no rate is proved.

* **108.42. Consistency of Brenier maps.** Let
  $\mu\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous, let
  $\nu,\nu_n\in\mathcal P_2(\mathbb R^d)$ with $W_2(\nu_n,\nu)\to0$, and let
  $T$, $T_n$ be the Brenier maps from $\mu$ to $\nu$ and to $\nu_n$. Then
  $T_n\to T$ in $L^2(\mu)$. TauCeti has Brenier's theorem, stability of the
  primal problem under varying marginals, and the equivalence of weak
  convergence of graph plans with convergence in measure of the maps; the
  conclusion, which also needs convergence of second moments to pass from
  convergence in measure to $L^2(\mu)$, is not stated.

* **108.43. Gromov–Wasserstein distance.** For $p\ge1$ and compact metric
  spaces with Borel probabilities, put
  $$\mathop{\mathrm{GW}}_p(\mu,\nu)^p=\inf_{\pi\in\Pi(\mu,\nu)}
  \iint|d_X(x,x')-d_Y(y,y')|^p\,d\pi(x,y)\,d\pi(x',y').$$
  Then $\mathop{\mathrm{GW}}_p$ is a metric on compact metric probability
  spaces modulo measure-preserving isometries of their supports; in
  particular $\mathop{\mathrm{GW}}_p(\mu,\nu)=0$ exactly when some isometry of
  $\mathop{\mathrm{supp}}\mu$ onto $\mathop{\mathrm{supp}}\nu$ pushes $\mu$ to
  $\nu$. TauCeti defines $\mathop{\mathrm{GW}}_p$ with this normalization,
  proves it is an extended pseudodistance, proves that it vanishes exactly
  on weakly isomorphic measured kernels (identified almost everywhere by a
  coupling), and makes the measured kernels of finite $p$-size on standard
  Borel probability spaces, modulo weak isomorphism, a metric space; missing
  is the upgrade from weak isomorphism to an isometry of supports for compact
  metric spaces.

For $\varepsilon>0$ let $\mathop{\mathrm{OT}}_\varepsilon$ be the entropic
transport cost and
$S_\varepsilon(\mu,\nu)=\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)
-\frac12\mathop{\mathrm{OT}}_\varepsilon(\mu,\mu)
-\frac12\mathop{\mathrm{OT}}_\varepsilon(\nu,\nu)$ the **debiased Sinkhorn
divergence**.

* **108.44. Debiased Sinkhorn divergence.** Let $X$ be a compact metric
  space, $\varepsilon>0$, and $c$ a symmetric Lipschitz cost on $X\times X$
  such that $e^{-c/\varepsilon}$ is a positive definite universal kernel (for
  example quadratic cost on a compact subset of $\mathbb R^d$). Then for
  probabilities on $X$, $S_\varepsilon(\mu,\nu)\ge0$ with equality exactly
  when $\mu=\nu$, and $S_\varepsilon(\mu_n,\mu)\to0$ if and only if
  $\mu_n\Rightarrow\mu$. TauCeti defines $S_\varepsilon$ for costs with
  values in $[0,\infty]$ and proves the first assertion for bounded
  measurable costs on a compact space whose Gibbs kernel
  $e^{-c/\varepsilon}$ is jointly continuous and positive definite:
  $S_\varepsilon(\mu,\nu)\ge0$, and, when the space is moreover compact
  metrizable with its Borel $\sigma$-algebra and the Gibbs kernel is
  universal, $S_\varepsilon(\mu,\nu)=0$ exactly when $\mu=\nu$. A real-valued
  Lipschitz cost reduces to this case by adding a constant, a reduction that
  is not stated. The metrization of weak convergence by $S_\varepsilon$ is
  absent, and so is the universality of the Gaussian kernel needed for the
  quadratic-cost example.

### Explicit geometries and empirical inference

* **108.46. Gaussian transport and barycenters.** For covariance matrices
  $A,B\ge0$,
  $$W_2^2(N(m,A),N(n,B))=\|m-n\|^2+\mathop{\mathrm{tr}}
  [A+B-2(A^{1/2}BA^{1/2})^{1/2}],$$
  and if $A>0$ the optimal map is
  $x\mapsto n+A^{-1/2}(A^{1/2}BA^{1/2})^{1/2}A^{-1/2}(x-m)$. For finitely many
  Gaussian laws $N(m_i,A_i)$ with $A_i>0$ and weights $\lambda_i\ge0$ summing
  to one, the barycenter is unique and Gaussian, with mean
  $\sum_i\lambda_im_i$ and covariance the unique positive definite solution of
  $$\bar A=\sum_i\lambda_i(\bar A^{1/2}A_i\bar A^{1/2})^{1/2};$$
  if the $A_i$ commute, $\bar A=(\sum_i\lambda_iA_i^{1/2})^2$. TauCeti proves
  the distance formula and optimal affine map when $A$ is positive definite,
  and the barycenter of two Gaussian laws through the geodesic. For finitely
  many Gaussian laws with positive semidefinite covariances it proves that,
  if a positive definite $\bar A$ solves the fixed-point equation, the
  Gaussian law with mean $\sum_i\lambda_im_i$ and covariance $\bar A$ is a
  barycenter, the only one when some covariance with positive weight is
  positive definite. Missing are the distance formula with both covariances
  singular, the existence of a positive definite solution of the fixed-point
  equation, and the commuting case; the uniqueness of the solution follows
  from the uniqueness of the barycenter.

* **108.47. One-dimensional empirical transport limit.** Let $\mu$ be
  supported on $[a,b]$ with a continuous density $f$ bounded above and below
  by positive constants there, and distribution function $F$. Then
  $$nW_2^2(\mu_n,\mu)\Rightarrow
  \int_0^1\frac{B^0(u)^2}{f(F^{-1}(u))^2}\,du,$$
  with $B^0$ a standard Brownian bridge, so $W_2(\mu_n,\mu)=O_P(n^{-1/2})$.
  TauCeti's quantile isometry expresses $W_2$ on the line through quantile
  functions; the Brownian bridge and the weak limit of the quantile process
  are absent.

### Minimax limits, smoothness, and smoothing

* **108.50. Minimax lower bounds for transport estimation.** Let $d\ge3$ and
  let $\lambda$ be the uniform law on $[0,1]^d$. Every probability supported
  on at most $n$ points is at $W_1$-distance at least $n^{-1/d}/(108\,d)$ from
  $\lambda$. For $n\ge8$ and every estimator $\tilde\mu_n$, that is, every
  measurable function of $n$ independent observations,
  $\sup_\mu\mathbb E_\mu W_1(\tilde\mu_n,\mu)\ge\frac1{16}(2n)^{-1/d}$, the
  supremum over probabilities supported in $[0,1]^d$. TauCeti defines the
  $N$-point Wasserstein quantization error and proves that best quantizers
  exist on proper spaces; no quantitative bound and no minimax framework are
  present.

On the torus $\mathbb T^d=\mathbb R^d/(2\pi\mathbb Z)^d$, $H^s$ ($s$ a
positive integer) consists of densities whose derivatives of order at most
$s$ are square integrable. The dual Lipschitz norm
$\widetilde W_1(\alpha,\beta)=\sup\{\int f\,d(\alpha-\beta):
\mathop{\mathrm{Lip}}f\le1\}$ extends $W_1$ to signed measures of equal mass,
and $W_p^{(\sigma)}(\mu,\nu)=W_p(\mu*N(0,\sigma^2I),\nu*N(0,\sigma^2I))$ is
the **smoothed Wasserstein distance**.

* **108.51. Smooth laws and smoothed distances.** Let $d\ge3$, let $\mu$ have
  a density on $\mathbb T^d$ with $H^s$ norm at most $L$, and let
  $\tilde\mu_n$ be the signed measure obtained by truncating the empirical
  Fourier series at frequencies $\|m\|\le M$, with $M\asymp n^{1/(d+2s)}$.
  Then $\mathbb E\widetilde W_1(\tilde\mu_n,\mu)\le Cn^{-(s+1)/(d+2s)}$, with
  $C$ depending only on $d,s,L$ and the constant in $M\asymp n^{1/(d+2s)}$,
  and a probability $\bar\mu_n$ minimizing $\widetilde W_1(\cdot,\tilde\mu_n)$
  satisfies $W_1(\bar\mu_n,\mu)\le2\widetilde W_1(\tilde\mu_n,\mu)$. For any
  $d\ge1$ and $\mu$ supported in $[-1,1]^d$,
  $\mathbb E W_1^{(\sigma)}(\mu_n,\mu)\le C_{\sigma,d}\,n^{-1/2}$. TauCeti
  proves that convolution with a common law does not increase $W_p$; the
  smoothed distance, its rate, and the torus estimator are absent.

### Estimation of transport maps

Let $\mu,\nu\in\mathcal P_2(\mathbb R^d)$ with $\mu$ absolutely continuous.
For convex $\phi$ with Legendre conjugate $\phi^*$, the **semidual
functional** is $\mathcal S(\phi)=\int\phi\,d\mu+\int\phi^*\,d\nu$, and the
**semidual estimator** $\nabla\hat\phi$ minimizes
$\int\phi\,d\mu_n+\int\phi^*\,d\nu_n$ over a class $\Phi$ of convex
potentials, from $n$ independent observations of each law.

* **108.53. Rates for transport-map estimation.** Let $\mu,\nu$ be supported
  in concentric closed balls of radii $r$ and $1$, respectively, where
  $0\le r<1$, with $\nu=(\nabla\varphi)_\#\mu$ and $\varphi\in\Phi$.
  Every potential of $\Phi$ is twice continuously differentiable on a
  neighbourhood of the closed unit ball; the potentials are uniformly
  bounded there, satisfy $\frac12I\preceq\nabla^2\phi\preceq2I$ on the
  closed ball, and have
  sup-norm covering numbers with
  $\log N(\varepsilon,\Phi)\lesssim\varepsilon^{-\gamma}\log(1+\varepsilon^{-1})$,
  $\gamma\in[0,1)$, where $\lesssim$ and $\asymp$ hide constants independent
  of $n$ and $\varepsilon$ but may depend on $1-r$. Then
  $\mathbb E\|\nabla\hat\phi-\nabla\varphi\|_{L^2(\mu)}^2\lesssim n^{-1/2}$;
  if moreover $\Phi$ is convex and $\mu$ satisfies a Poincaré inequality
  $\mathop{\mathrm{Var}}_\mu(h)\le C_P\int\|\nabla h\|^2\,d\mu$ for smooth $h$,
  the rate improves to $(\log n/n)^{2/(2+\gamma)}$. For $\mu$ with density
  bounded above and below on $[0,1]^d$, $T=\nabla f$ of Hölder order
  $\alpha>1$ with norm at most $R$ on a neighbourhood,
  $M^{-1}I\preceq DT\preceq MI$, and $T_\#\mu$ supported on $[0,1]^d$, the
  minimax risk satisfies
  $$\inf_{\hat T}\sup\mathbb E\|\hat T-T\|_{L^2(\mu)}^2\asymp
  n^{-2\alpha/(2\alpha-2+d)}\vee n^{-1},$$
  up to a factor $(\log n)^2$ in the upper bound, attained by a semidual
  estimator over truncated wavelet expansions. TauCeti has Brenier's theorem
  and Kantorovich duality; the semidual functional, its strong-convexity
  stability bounds, and all rates are absent.

### Entropic transport: duality and statistical rates

* **108.55. Dimension-free sample complexity of entropic transport.** Let
  $\mu,\nu$ be supported in a ball of radius $\frac12$ in $\mathbb R^d$, with
  quadratic cost, let $\mu_n,\nu_n$ be empirical measures of independent
  samples of size $n$, and let $\hat b$ be the entropic map between them,
  extended canonically off the sample. Then
  $$\mathbb E\bigl(\mathop{\mathrm{OT}}_\varepsilon(\mu_n,\nu_n)
  -\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)\bigr)^2\lesssim\frac1n,\qquad
  \bigl|\mathbb E\mathop{\mathrm{OT}}_\varepsilon(\mu_n,\nu_n)
  -\mathop{\mathrm{OT}}_\varepsilon(\mu,\nu)\bigr|\lesssim\frac1n,\qquad
  \mathbb E\|\hat b-b_\varepsilon\|_{L^2(\mu)}^2\lesssim\frac1n,$$
  with constants depending only on $\varepsilon$, not on $d$, $\mu$, $\nu$,
  or $n$. Here $b_\varepsilon(x)=\mathbb E_{\pi_\varepsilon}[Y\mid X=x]$ is
  the entropic map of the optimal entropic coupling $\pi_\varepsilon$.
  TauCeti proves strong entropic duality with attainment for bounded costs
  and the Sinkhorn fixed-point characterization, and it gives linear rates
  for the discrete Sinkhorn iteration in Hilbert's projective metric, a
  statement about the algorithm rather than about sampling; the entropic map
  and every sample-complexity bound are absent.

### Semidiscrete transport

Let $\mu\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous and
$\nu=\sum_{j=1}^mb_j\delta_{y_j}$ with distinct $y_j$ and $b_j>0$. For
quadratic cost $c$ and $g\in\mathbb R^m$ put
$g^c(x)=\min_j(c(x,y_j)-g_j)$, with **Laguerre cells**
$L_j(g)=\{x:c(x,y_j)-g_j\le c(x,y_k)-g_k\text{ for all }k\}$.

* **108.56. Semidiscrete dual.** The function
  $E(g)=\int g^c\,d\mu+\sum_jb_jg_j$ is concave, invariant under adding a
  constant to all $g_j$, and continuously differentiable with
  $\partial E/\partial g_j=b_j-\mu(L_j(g))$; its maximum is the optimal
  transport cost from $\mu$ to $\nu$. A vector $g$ is a maximizer exactly when
  $\mu(L_j(g))=b_j$ for all $j$, and then the map sending $L_j(g)$ to $y_j$ is
  the optimal transport map. TauCeti has the general $c$-transform and dual
  attainment; Laguerre cells, the differentiability of $E$, and the
  semidiscrete characterization are absent.

### Tangent space, linearization, and Fréchet means

Let $\gamma\in\mathcal P_2(\mathbb R^d)$ be absolutely continuous and let
$t_\gamma^\mu$ be the Brenier map from $\gamma$ to $\mu$. The tangent space
$\mathop{\mathrm{Tan}}_\gamma$ is the $L^2(\gamma;\mathbb R^d)$ closure of the
gradients of smooth compactly supported functions; the **log map** is
$\log_\gamma\mu=t_\gamma^\mu-\mathrm{id}$ and the **exponential map**
$\exp_\gamma r=(\mathrm{id}+r)_\#\gamma$. A family $\mathcal C$ of absolutely
continuous laws is **compatible** if $t_\gamma^\mu\circ t_\nu^\gamma=t_\nu^\mu$
in $L^2(\nu)$ for all $\gamma,\mu,\nu\in\mathcal C$. For laws
$\mu_1,\ldots,\mu_N\in\mathcal P_2(\mathbb R^d)$ put
$F(\gamma)=\frac1{2N}\sum_iW_2^2(\gamma,\mu_i)$.

* **108.57. Tangent-space linearization.** For absolutely continuous
  $\gamma$, $\|\log_\gamma\mu\|_{L^2(\gamma)}=W_2(\gamma,\mu)$,
  $s\mapsto\exp_\gamma(s\log_\gamma\mu)$, $0\le s\le1$, is the constant-speed
  geodesic from $\gamma$ to $\mu$, and
  $W_2(\mu,\nu)\le\|\log_\gamma\mu-\log_\gamma\nu\|_{L^2(\gamma)}$. On a
  compatible family containing $\gamma$ equality holds, so $\log_\gamma$ is an
  isometric embedding into a Hilbert space, and the Fréchet mean of compatible
  $\mu_1,\ldots,\mu_N$ is $(N^{-1}\sum_it_\gamma^{\mu_i})_\#\gamma$. A family
  of centered nondegenerate Gaussian laws containing the standard Gaussian is
  compatible exactly when the covariances commute. TauCeti defines the tangent
  space as a closure of gradients, proves the coupling bound through
  pushforwards, the displacement geodesics, and the one-dimensional quantile
  isometry; missing are the log and exponential maps as such, compatibility,
  the isometric embedding with the barycenter formula, and the Gaussian
  criterion.

* **108.58. First-order conditions for barycenters.** At absolutely
  continuous $\gamma$, $F$ is Fréchet differentiable with gradient
  $F'(\gamma)=-N^{-1}\sum_i(t_\gamma^{\mu_i}-\mathrm{id})
  \in\mathop{\mathrm{Tan}}_\gamma$, in the sense that
  $F(\nu)-F(\gamma)-\langle F'(\gamma),\log_\gamma\nu\rangle_{L^2(\gamma)}
  =o(W_2(\nu,\gamma))$. A **Karcher mean** is an absolutely continuous
  $\gamma$ with $F'(\gamma)=0$. If one $\mu_i$ has a bounded density, the
  Fréchet mean is absolutely continuous and hence a Karcher mean. Conversely,
  let $U$ be open and convex, let the $\mu_i$ and a Karcher mean $\gamma$ be
  supported in $U$ with bounded strictly positive densities there, and
  suppose that either $U=\mathbb R^d$ and the densities are Hölder continuous,
  or $U$ is bounded and the densities are bounded below on $U$; then $\gamma$
  is the Fréchet mean. For absolutely continuous $\mu_i$, if the closed convex
  potentials $\phi_i$ of $t_\gamma^{\mu_i}$ satisfy
  $N^{-1}\sum_i\phi_i\le\frac12\|x\|^2$ everywhere with equality
  $\gamma$-almost everywhere, then $\gamma$ is the unique Fréchet mean.
  TauCeti defines the Wasserstein subdifferential and proves existence and
  Euclidean uniqueness of barycenters; differentiability of $W_2^2$ at
  absolutely continuous laws, absolute continuity of the barycenter, and the
  sufficiency criteria are absent.

* **108.59. Procrustes iteration for barycenters.** From an absolutely
  continuous $\gamma_0$ put
  $\gamma_{j+1}=(N^{-1}\sum_it_{\gamma_j}^{\mu_i})_\#\gamma_j
  =\exp_{\gamma_j}(-F'(\gamma_j))$. For absolutely continuous $\gamma$ and
  $\tau\in[0,1]$, $\gamma_\tau=\exp_\gamma(-\tau F'(\gamma))$ is absolutely
  continuous and
  $F(\gamma_\tau)-F(\gamma)\le-\|F'(\gamma)\|_{L^2(\gamma)}^2(\tau-\tau^2/2)$.
  If one $\mu_i$ has a bounded density, the iterates stay in a $W_2$-compact
  set and every limit point is a Karcher mean; if moreover $F$ has a unique
  stationary point, $W_2(\gamma_j,\bar\mu)\to0$ for the Fréchet mean
  $\bar\mu$, and $t_{\gamma_j}^{\mu_i}\to t_{\bar\mu}^{\mu_i}$ uniformly on
  compact subsets of a set of full $\bar\mu$-measure. For centered Gaussian
  $\mu_i$ with one covariance nonsingular and a nonsingular centered Gaussian
  $\gamma_0$, the iterates converge to the Gaussian barycenter of 108.46.
  Absent from all three libraries.

### Kernel mean embeddings and integral probability metrics

For independent samples of equal size $n\ge2$, the unbiased estimator is
$$\mathop{\mathrm{MMD}}_{u,n}^2
=\frac{\sum_{i\ne j}k(X_i,X_j)+\sum_{i\ne j}k(Y_i,Y_j)}{n(n-1)}
-\frac2{n^2}\sum_{i,j}k(X_i,Y_j),$$
and the biased estimator is
$\mathop{\mathrm{MMD}}_{b,n}^2=\|\Phi(\mu_n)-\Phi(\nu_n)\|_{\mathcal H}^2$.
Let $(\lambda_j)$ be the eigenvalues on $L^2(\mu)$ of the integral operator of
the centered kernel
$\tilde k(x,y)=k(x,y)-\mathbb Ek(x,X')-\mathbb Ek(X,y)+\mathbb Ek(X,X')$.

* **108.61. Limits of the empirical discrepancy.** For a bounded continuous
  kernel on a Polish space with separable reproducing-kernel Hilbert space,
  under $\mu=\nu$,
  $$n\mathop{\mathrm{MMD}}_{u,n}^2\Rightarrow2\sum_j\lambda_j(Z_j^2-1),\qquad
  n\mathop{\mathrm{MMD}}_{b,n}^2\Rightarrow2\sum_j\lambda_jZ_j^2,$$
  with $Z_j$ independent standard normals. Under a fixed alternative, with
  $\Delta=\Phi(\mu)-\Phi(\nu)$,
  $\sqrt n(\mathop{\mathrm{MMD}}_{u,n}^2-\|\Delta\|_{\mathcal H}^2)$
  converges in distribution to a centered normal law with variance
  $4\mathop{\mathrm{Var}}_\mu\langle k(X,\cdot),\Delta\rangle
  +4\mathop{\mathrm{Var}}_\nu\langle k(Y,\cdot),\Delta\rangle$ (the point mass
  at $0$ when it vanishes). TauCeti has the mean embedding and the
  double-integral formula for $\mathop{\mathrm{MMD}}^2$; $U$-statistics, their
  degenerate limits, and the spectral expansion of the centered kernel are
  absent.

On $\mathbb R^d$, with $X,X'\sim\mu$ and $Y,Y'\sim\nu$ all independent, the
**energy distance** is
$D^2(\mu,\nu)=2\mathbb E\|X-Y\|-\mathbb E\|X-X'\|-\mathbb E\|Y-Y'\|$. For a
pair $(X,Y)$ with finite second moments, let $a(x,x')$ be $\|x-x'\|$ doubly
centered under the law of $X$, define $b$ similarly, and put
$\mathcal V^2(X,Y)=\mathbb E[a(X,X')b(Y,Y')]$ for independent copies of the
pair (**distance covariance**). The **Hilbert–Schmidt independence
criterion** $\mathop{\mathrm{HSIC}}_{k,\ell}(X,Y)$ is the squared
Hilbert–Schmidt norm of the cross-covariance operator, equivalently the
squared MMD between the joint law and the product of the marginals for the
product kernel $k\otimes\ell$.

* **108.62. Energy distance and independence.** For laws on $\mathbb R^d$
  with finite first moment, $D^2(\mu,\nu)\ge0$ with equality exactly when
  $\mu=\nu$, and $D^2(\mu,\nu)=2\mathop{\mathrm{MMD}}_{k_0}(\mu,\nu)^2$ for
  $k_0(x,y)=\frac12(\|x\|+\|y\|-\|x-y\|)$. With finite second moments,
  $\mathcal V^2(X,Y)\ge0$, it vanishes exactly at independence, and
  $\mathcal V^2(X,Y)=4\mathop{\mathrm{HSIC}}_{k_0,\ell_0}(X,Y)$ for the
  distance-induced kernels on the two coordinates. Absent from all three
  libraries; the conditionally negative definite kernel $\|x-y\|$ is not
  treated.

* **108.63. Hilbert–Schmidt independence criterion.** For bounded continuous
  kernels whose product kernel is characteristic on the product space (as for
  Gaussian kernels on Euclidean coordinates), HSIC vanishes if and only if
  $X$ and $Y$ are independent. Its unbiased estimator from paired
  observations is a $U$-statistic of order four; under independence its first
  Hoeffding projection vanishes and $n$ times it converges in distribution to
  $\sum_{r,s}\lambda_r\eta_s(Z_{rs}^2-1)$, with $\lambda_r,\eta_s$ the
  eigenvalues of the two centered marginal kernel operators and $Z_{rs}$
  independent standard normals; under dependence, $\sqrt n$ times its
  deviation from HSIC converges in distribution to a centered normal law,
  possibly the point mass at $0$. Cross-covariance operators, HSIC, and its
  limits are absent from all three libraries.

### Characteristic kernels and comparison of metrics

A bounded measurable kernel $k$ is **integrally strictly positive definite**
if $\iint k\,d\eta\,d\eta>0$ for every finite nonzero signed Borel measure
$\eta$. A continuous kernel on a compact metric space is **universal** if its
reproducing-kernel Hilbert space is dense in the continuous functions.

* **108.68. Criteria for characteristic kernels.** For a bounded measurable
  kernel, there are probabilities $\mu\ne\nu$ with
  $\mathop{\mathrm{MMD}}(\mu,\nu)=0$ exactly when some finite nonzero signed
  measure $\eta$ of total mass zero has $\iint k\,d\eta\,d\eta=0$. Hence:
  (a) integrally strictly positive definite kernels are characteristic, for
  example the Gaussian, Laplace, and inverse multiquadric kernels
  $(c^2+\|x-y\|^2)^{-\beta}$, $c,\beta>0$, on $\mathbb R^d$;
  (b) universal kernels on compact metric spaces are characteristic;
  (c) for $k(x,y)=\psi(x-y)$ with $\psi$ bounded, continuous, and positive
  definite on $\mathbb R^d$ with spectral measure $\Lambda$, $k$ is
  characteristic if and only if $\mathop{\mathrm{supp}}\Lambda=\mathbb R^d$;
  in particular every nonzero such $\psi$ of compact support is
  characteristic, and the sinc kernel is not;
  (d) for the unbounded kernel $k(x,y)=(1+x^\top y)^2$ and laws with finite
  fourth moments,
  $\mathop{\mathrm{MMD}}^2(\mu,\nu)=2\|m_\mu-m_\nu\|^2
  +\|\Sigma_\mu-\Sigma_\nu+m_\mu m_\mu^\top-m_\nu m_\nu^\top\|_F^2$, which
  vanishes for distinct laws with equal first two moments. TauCeti proves (b)
  on compact metrizable spaces, Bochner's theorem, and positive definiteness
  of the Gaussian kernel, and Mathlib has Fourier uniqueness of finite
  measures; the general criterion, (a), the spectral characterization (c),
  and the example (d) are absent.

* **108.70. Metrization of weak convergence.** For a bounded continuous
  characteristic kernel on a Polish space, $\mu_n\Rightarrow\mu$ implies
  $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$; conversely, if $(\mu_n)$ is tight
  and $\mathop{\mathrm{MMD}}(\mu_n,\mu)\to0$, then $\mu_n\Rightarrow\mu$.
  Without tightness: (a) on a compact metric space the MMD of a continuous
  universal kernel metrizes the weak topology on probabilities; (b) on
  $\mathbb R^d$, if $k(x,y)=\psi(x-y)$ with $\psi\in C_0\cap L^1$ real,
  bounded and strictly positive definite, and
  $\int(\hat\psi(\omega)(1+\|\omega\|^2)^l)^{-1}\,d\omega<\infty$ for some
  integer $l$, the MMD metrizes weak convergence (this covers the Matérn
  family but not the Gaussian kernel). Mathlib's Prokhorov theorem and
  TauCeti's kernel mean embedding with its double-integral formula give the
  tight case by a short subsequence argument, and the forward implication
  follows from weak convergence of $\mu_n\otimes\mu_n$ against the bounded
  continuous $k$. TauCeti characterizes weak convergence on Polish spaces by
  uniform convergence of integrals of bounded $1$-Lipschitz functions and by
  truncated transport costs, but MMD is not defined on probability measures
  in any of the three libraries, and the metrization statements (a) and (b)
  are absent.

### Kernel Stein discrepancies

Let $P$ have a positive $C^1$ density $p$ on $\mathbb R^d$ with score
$b=\nabla\log p$. The **Langevin Stein operator** is
$(\mathcal T_Pg)(x)=\langle g(x),b(x)\rangle+\nabla\cdot g(x)$ for
$g:\mathbb R^d\to\mathbb R^d$. The **kernel Stein set** consists of
$g=(g_1,\ldots,g_d)$ with $g_j\in\mathcal H$ and
$\sum_j\|g_j\|_{\mathcal H}^2\le1$, and
$\mathop{\mathrm{KSD}}(\mu)=\sup_g|\mathbb E_\mu(\mathcal T_Pg)(X)|$. The
**Stein kernel** is
$$k_P(x,y)=\sum_{j=1}^d\bigl[b_j(x)b_j(y)k(x,y)+b_j(x)\partial_{y_j}k(x,y)
+b_j(y)\partial_{x_j}k(x,y)+\partial_{x_j}\partial_{y_j}k(x,y)\bigr].$$
$P$ is **distantly dissipative** if $\liminf_{r\to\infty}\kappa(r)>0$, where
$\kappa(r)=\inf\{-2\langle b(x)-b(y),x-y\rangle/\|x-y\|^2:\|x-y\|=r\}$.

* **108.71. Kernel Stein discrepancy.** Let $k$ be bounded with bounded
  continuous derivatives $\partial_{x_j}k$, $\partial_{y_j}k$,
  $\partial_{x_j}\partial_{y_j}k$, and let the score be $P$-integrable. Then
  $\mathbb E_P(\mathcal T_Pg)(Z)=0$ for every $g$ in the kernel Stein set,
  and if $\mathbb E_\mu k_P(X,X)<\infty$,
  $$\mathop{\mathrm{KSD}}(\mu)^2=\mathbb E\,k_P(X,X')$$
  for independent $X,X'$ of law $\mu$. Since $\mathbb E_Pk_P(Z,y)=0$ for
  every $y$, this is the squared MMD between $\mu$ and $P$ for the kernel
  $k_P$. Stein operators, Stein kernels, and the discrepancy are absent from
  all three libraries.

* **108.72. Convergence control by kernel Stein discrepancies.** Let $P$ be
  distantly dissipative with Lipschitz score. (a) If $k$ has bounded
  continuous derivatives up to order two in each argument and
  $\mathbb E_P\|b(Z)\|^2<\infty$, then $W_1(\mu_m,P)\to0$ implies
  $\mathop{\mathrm{KSD}}(\mu_m)\to0$. (b) For the inverse multiquadric kernel
  $(c^2+\|x-y\|^2)^\beta$ with $c>0$, $\beta\in(-1,0)$,
  $\mathop{\mathrm{KSD}}(\mu_m)\to0$ implies $\mu_m\Rightarrow P$. (c) For a
  translation-invariant $C^2$ kernel with nonvanishing generalized Fourier
  transform, the same conclusion holds for uniformly tight sequences, and for
  all sequences when $d=1$. (d) Let $d\ge3$ and $P=N(0,I)$, let $k$ be
  bounded with bounded continuous $\nabla_xk$, $\nabla_yk$ and
  $\langle\nabla_x,\nabla_y\rangle k$, and let
  $\gamma(r)=\sup\{\max(|k(x,y)|,\|\nabla_xk(x,y)\|,
  |\langle\nabla_x,\nabla_y\rangle k(x,y)|):\|x-y\|\ge r\}$ satisfy
  $\gamma(r)=o(r^{-\alpha})$ with $\alpha=(\frac12-\frac1d)^{-1}$; then some
  sequence with $\mathop{\mathrm{KSD}}(\mu_m)\to0$ does not converge weakly to
  $P$ (this includes the Gaussian, Matérn, and Wendland kernels). Absent from
  all three libraries.

### Conditional embeddings and random features

* **108.74. Random Fourier features.** Let $k(x,y)=\psi(x-y)$ be continuous
  and positive definite on $\mathbb R^d$ with $\psi(0)=1$, so its spectral
  measure $\Lambda$ is a probability. Let $\omega_1,\ldots,\omega_D\sim\Lambda$
  and $b_1,\ldots,b_D$ uniform on $[0,2\pi]$ be independent, and put
  $z(x)=\sqrt{2/D}\,(\cos(\omega_j^\top x+b_j))_{j\le D}$. Then
  $\mathbb E\,z(x)^\top z(y)=k(x,y)$, and for fixed $x,y$,
  $\mathbb P(|z(x)^\top z(y)-k(x,y)|\ge\varepsilon)\le2e^{-D\varepsilon^2/8}$.
  If $\sigma^2=\int\|\omega\|^2\Lambda(d\omega)<\infty$ and
  $M\subset\mathbb R^d$ is compact with $\sigma\mathop{\mathrm{diam}}M\ge
  \varepsilon$, then
  $$\mathbb P\Bigl(\sup_{x,y\in M}|z(x)^\top z(y)-k(x,y)|\ge\varepsilon\Bigr)
  \le98\Bigl(\frac{\sigma\mathop{\mathrm{diam}}M}{\varepsilon}\Bigr)^2
  \exp\Bigl(-\frac{D\varepsilon^2}{32(d+1)}\Bigr),$$
  and on the event that this supremum is below $\varepsilon$,
  $|\mathop{\mathrm{MMD}}_z(\mu,\nu)^2-\mathop{\mathrm{MMD}}_k(\mu,\nu)^2|
  \le4\varepsilon$ for all probabilities $\mu,\nu$ on $M$, where
  $\mathop{\mathrm{MMD}}_z(\mu,\nu)^2=\|\int z\,d\mu-\int z\,d\nu\|^2$.
  TauCeti's probability form of Bochner's theorem gives the unbiasedness
  identity by a product-to-sum computation, and Mathlib's Hoeffding
  inequality then gives the pointwise bound, since each summand of
  $z(x)^\top z(y)$ is $D^{-1}$ times a variable in $[-2,2]$; neither is
  stated. The uniform bound needs a net argument on $M\times M$ with a
  Lipschitz control of the error; TauCeti's volumetric bound on covering
  numbers of bounded sets in finite-dimensional normed spaces supplies the
  nets, and the argument is absent.

