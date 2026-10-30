# Synopsis: Machine-learning models, representation, and sequential decisions

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-113).

This synopsis follows Section 113. Subdivision 113A is ensembles and
probabilistic models. Subdivision 113B is approximation and the analysis of
trained networks. Subdivision 113C is networks. Subdivision 113D is bandits
and reinforcement learning. Subdivision 113E is privacy, fairness, and
shift. Uniform convergence, Rademacher complexity, and full-information
regret are [SYNOPSIS107](SYNOPSIS107.md), items 7–11. The representer
theorem and kernel ridge regression are [SYNOPSIS104](SYNOPSIS104.md),
item 8. Simple kriging is [SYNOPSIS108](SYNOPSIS108.md), item 18. The
evidence lower bound is [SYNOPSIS105](SYNOPSIS105.md), item 15. Exchangeability
of sequences is [CKMA SYNOPSIS06](../lean-CKMA/SYNOPSIS06.md), item 55.
Ridge-function approximation in the analytic sense is CKMA Section 47.
Continuous-time stochastic control remains in CKMA Section 8. Optimization
algorithms are in Section 114.

The posterior mean of a Gaussian process with covariance kernel $k$ and
noise variance $\sigma^2$ is the kernel ridge regressor of SYNOPSIS104,
item 8, with $\lambda=\sigma^2/n$ for its averaged-loss convention, and it is the simple-kriging
predictor of SYNOPSIS108, item 18. A variational autoencoder maximizes the
evidence lower bound of SYNOPSIS105, item 15, with an encoder that maps each
observation to the parameter of the variational factor; the
reparameterization $z=\mu(x)+\sigma(x)\varepsilon$ makes the gradient of
that bound an ordinary expectation under a parameter-free noise law.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-113a"></a>

## 113A. General Foundations, Probabilistic Modelling, and Ensembles

Let $X$ take values in $\mathbb R^d$ with $\mathbb E\|X\|^2<\infty$,
and fix $k\ge1$. The $k$-means criterion of a set of centers $c$ is
$\mathbb E\bigl(\min_j\|X-c_j\|^2\bigr)$.

* **1. Consistency of $k$-means.** Suppose $\mathbb E\|X\|^2<\infty$,
  the support contains at least $k$ distinct points, and the population
  optimal $k$-center set is unique up to labels. Then empirical global
  minimizing center sets converge almost surely to that set, up to
  permutation. The nondegeneracy prevents unused centers from escaping
  to infinity. This concerns global minimizers; convergence of Lloyd's
  iteration to a stationary configuration does not imply it finds them.

A binary tree $T$ grown on a training sample has resubstitution error
$R(T)$ and $|T|$ terminal nodes. For $\alpha\ge0$ the **cost-complexity**
is $R_\alpha(T)=R(T)+\alpha|T|$.

* **2. Cost-complexity pruning.** For each $\alpha$ there is a smallest
  subtree minimizing $R_\alpha$. As $\alpha$ increases through $[0,\infty)$,
  these smallest minimizers form a nested decreasing sequence of subtrees.

For squared error, let $f^*(X)=\mathbb E[Y\mid X]$, with $Y\in L^2$,
and put $r_m=f^*-f_m$. The excess prediction risk is $\|r_m\|_2^2$.
A base learner $h_m$ is a nonzero square-integrable function of $X$.

* **3. Descent of gradient boosting.** Suppose
  $\langle r_m,h_m\rangle\ge\gamma\|r_m\|_2\|h_m\|_2$ for a fixed
  $\gamma>0$. Choose the least-squares coefficient
  $a_m=\langle r_m,h_m\rangle/\|h_m\|_2^2$ and update
  $f_{m+1}=f_m+\nu a_m h_m$, with $0<\nu<2$. Then
  $$\|r_{m+1}\|_2^2\le
  (1-\nu(2-\nu)\gamma^2)\|r_m\|_2^2.$$
  Thus the excess risk decreases geometrically. Scaling each learner
  properly is essential; positive correlation and comparable norms alone
  do not imply descent for an arbitrary fixed step. Irreducible response
  noise is excluded from the excess risk.

For a finite-state pairwise graphical model with positive node and edge
potentials, the **Bethe free energy** uses local node and edge marginals,
subject to normalization and marginal-consistency constraints. Its entropy
approximation is $H_B=\sum_{\{i,j\}\in E}H(b_{ij})
-\sum_i(d_i-1)H(b_i)$. **Belief propagation** updates messages along edges.

* **4. Belief propagation and the Bethe free energy.** Positive
  belief-propagation fixed points correspond to interior stationary
  points of the constrained Bethe free energy. Stationarity need not
  mean global minimality or convergence of the message iteration on a
  graph with cycles. Restricting local beliefs to products
  $b_{ij}=b_i b_j$ gives the fully factorized mean-field objective,
  related to the evidence lower bound in SYNOPSIS105, item 15.
  Exact inference on trees is item 28 below.

* **5. Consistency of response-independent forests.** Consider tree
  partitions formed independently of responses, with leaf averages
  computed from an independent sample of identically distributed pairs.
  Suppose the diameter of the leaf containing an independent query $X$
  tends to zero in probability,
  its estimation-sample size tends to infinity, and the resulting
  nonnegative weights sum to one and satisfy the bounded-averaging
  condition
  $$\mathbb E\sum_iw_{ni}(X)g(X_i)\le C\mathbb E g(X)$$
  for all nonnegative bounded $g$, with a fixed $C$ and independent
  query $X$. Require also
  $\mathbb E\sum_iw_{ni}(X)1_{\{\|X_i-X\|>\eta\}}\to0$ for every
  $\eta>0$ and $\mathbb E\max_iw_{ni}(X)\to0$.
  Then the tree regression, and averages of trees drawn from the same
  construction, are consistent in integrated mean squared error for
  $Y\in L^2$. Honesty and growing leaf size
  without shrinking cells are insufficient. Response-adaptive Breiman
  forests require separate model and splitting assumptions, such as
  those in the additive-model theorem of Scornet, Biau, and Vert.

### Prediction losses and ensemble structure

* **26. Proper prediction losses.** For a categorical response with
  conditional probabilities $p_j(x)$, expected logarithmic loss of a
  reported probability vector $q$ equals
  $$-\sum_jp_j\log q_j
  =-\sum_jp_j\log p_j+D(p\|q).$$
  It is minimized by the true probabilities. For the Brier loss
  $\sum_j(q_j-1_{\{Y=j\}})^2$, the excess conditional risk is
  $\sum_j(q_j-p_j)^2$. Thus these losses target conditional
  distributions, whereas $0$–$1$ loss only determines a most probable
  label. Bayes classification risk is SYNOPSIS107, item 20.

* **27. Variance of an ensemble average.** If $B$ square-integrable
  predictions have the same variance $\sigma^2$ and pairwise correlation
  $\rho$, their average has variance
  $$\sigma^2\left(\rho+\frac{1-\rho}{B}\right).$$
  Independently randomized learners on the same training sample can
  remain correlated after averaging over that common sample. Under
  squared loss the full risk also includes squared bias; averaging
  controls variance without automatically removing bias or establishing
  consistency. This explains the separate shrinking-cell assumptions
  in item 5.

* **28. Exact belief propagation on a tree.** For the positive pairwise
  model of item 4 on a tree, messages satisfy
  $$m_{i\to j}(x_j)\propto\sum_{x_i}\psi_i(x_i)\psi_{ij}(x_i,x_j)
  \prod_{\ell\in N(i)\setminus\{j\}}m_{\ell\to i}(x_i).$$
  A pass from leaves to a root and back computes exact node and edge
  marginals; the node marginal is proportional to
  $\psi_i(x_i)\prod_{j\in N(i)}m_{j\to i}(x_i)$.
  Local consistency is sufficient for globally realizable beliefs on
  a tree, and the Bethe entropy is exact there. Cycles remove these
  guarantees.

<a id="synopsis-113b"></a>

## 113B. Deep Learning: Architectures, Approximation, and Training Theory

Density of one-hidden-layer networks in $C(K)$, for a nonpolynomial
continuous activation, is [CKMA SYNOPSIS47](../lean-CKMA/SYNOPSIS47.md),
item 76.

* **6. Barron's rate.** Suppose $f\in L^1(\mathbb R^d)$ has a finite
  Fourier moment
  $C_f=\int_{\mathbb R^d}\|\omega\|\,|\hat f(\omega)|\,d\omega$. On a design
  supported in a fixed ball there is a one-hidden-layer network with $n$
  sigmoidal units and an output bias whose $L^2$ error is at most a
  constant, depending on the ball radius and activation, times
  $C_f n^{-1/2}$. ReLU units also admit this form of the bound.
  The exponent is $-1/2$ in every dimension $d$; finiteness or size
  of $C_f$ remains a restriction on the target function.

* **7. Deep networks and compositional classes.** In nonparametric
  regression with design density bounded above and below by positive
  constants on a compact cube, Gaussian noise, and regression
  functions that are compositions of bounded Hölder maps, let stage $i$
  have smoothness $\beta_i$ and at most $t_i$ active input coordinates
  per component. Put
  $$\beta_i^*=\beta_i\prod_{j>i}\min(\beta_j,1).$$
  Under the usual class nondegeneracy conditions the minimax integrated
  squared-error rate is
  $\max_i n^{-2\beta_i^*/(2\beta_i^*+t_i)}$.
  Suitably constrained sparse ReLU least-squares estimators attain this
  rate up to logarithmic factors. The statement concerns specified
  statistical estimators and classes, not the outcome of arbitrary
  network training.

In the **neural tangent** parameterization the output weights and the inner
weights are scaled so that a gradient step remains of order one as the width
tends to infinity. The **neural tangent kernel** is the Gram matrix of the
output's gradient with respect to the parameters.

* **8. Neural tangent kernel.** In the standard neural-tangent scaling
  of a fully connected network with independent Gaussian initialization,
  assume fixed depth, a fixed finite training set, and a smooth activation
  with bounded derivatives as required for the kernel limit. As the
  hidden widths tend to infinity, the empirical tangent Gram matrix
  converges to a deterministic matrix $\Theta$. For squared loss and
  gradient flow, on fixed finite time intervals the limiting training
  outputs satisfy
  $$\dot f_t=-\Theta(f_t-y)/n.$$
  Linearization is valid in this width limit under its regularity
  hypotheses; it is not a generic property of every parameterization or
  every duration of finite-width training.

Let $x_i$ be independent standard normal vectors in $\mathbb R^p$, let
$y_i=x_i^\top\beta+\varepsilon_i$ with independent centered errors
of variance $\sigma^2$, independent of the design, and let $\hat\beta$ be the minimum-$\ell^2$-norm least
squares estimator. The **excess prediction risk** is
$\mathbb E(x^\top\hat\beta-x^\top\beta)^2$, averaging over the training
data and an independent test point $x$. The parameter vectors are
deterministic. Write $\gamma=\lim p/n$.

* **9. Ridgeless least squares.** In the isotropic Gaussian design,
  the expected excess prediction risk is exactly
  $$\frac{\sigma^2p}{n-p-1}\quad(n>p+1),$$
  and
  $$\|\beta\|^2(1-n/p)+\frac{\sigma^2 n}{p-n-1}\quad(p>n+1).$$
  If $p/n\to\gamma\in(0,\infty)\setminus\{1\}$ and
  $\|\beta\|^2\to r^2$, the respective limits are
  $\sigma^2\gamma/(1-\gamma)$ and
  $r^2(1-1/\gamma)+\sigma^2/(\gamma-1)$.
  The inverse-Wishart denominators expose the risk singularity near
  interpolation; existence of an interpolating estimator alone does
  not bound its prediction risk.

For a generator density $p_g$ and a data density $p$, the **generative
adversarial** value of a discriminator $D$ with values in $[0,1]$ is
$$\mathbb E_p\log D(X)+\mathbb E_{p_g}\log\bigl(1-D(X)\bigr).$$

* **10. Equilibrium of a generative adversary.** For fixed $p_g$ the optimal
  discriminator is $D^\star(x)=p(x)/\bigl(p(x)+p_g(x)\bigr)$ wherever the sum
  is positive. Its value equals $-\log4+2\,\mathop{\mathrm{JSD}}(p,p_g)$,
  where $\mathop{\mathrm{JSD}}$ is the Jensen–Shannon divergence,
  with the usual $0\log0=0$ convention. If $D$ is restricted to
  $(0,1)$, this can be a supremum rather than an attained maximum.
  The value
  is minimized, with minimum $-\log4$, if and only if $p_g=p$.

### Probabilistic output layers and kernel prediction

* **29. Softmax and cross-entropy.** For logits $z\in\mathbb R^K$,
  let $A(z)=\log\sum_j e^{z_j}$ and $q_j=e^{z_j-A(z)}$.
  For a one-hot observed label $y$, logarithmic loss is $A(z)-y^\top z$,
  with gradient $q-y$ and Hessian
  $$\mathop{\mathrm{diag}}(q)-qq^\top.$$
  The Hessian is positive semidefinite and vanishes in the direction
  $1$, reflecting invariance to adding a constant to all logits.
  Convexity in logits does not imply convexity in the parameters of
  a network producing them. The cumulant calculation is the
  exponential-family identity of SYNOPSIS101, item 4.

* **30. Gaussian-process posterior prediction.** Let a zero-mean Gaussian
  process have kernel $k$, and observe
  $y_i=f(x_i)+\varepsilon_i$ with independent $N(0,\sigma^2)$ noise,
  $\sigma^2>0$. For $K=(k(x_i,x_j))$ and
  $k_x=(k(x_i,x))_i$, the posterior mean and covariance are
  $$m(x)=k_x^\top(K+\sigma^2I)^{-1}y,$$
  $$k_{\mathrm{post}}(x,x')
  =k(x,x')-k_x^\top(K+\sigma^2I)^{-1}k_{x'}.$$
  Future noisy-response variance adds $\sigma^2$. The posterior mean
  is kernel ridge regression with penalty $\lambda=\sigma^2/n$ under
  the averaged squared-loss convention. This equality of means does
  not identify a frequentist confidence band with a posterior band.

<a id="synopsis-113c"></a>

## 113C. Networks and Graph Representation Learning

In the **symmetric two-group stochastic block model**, $n$ vertices are
split equally at random into two groups, edges are independent, and the
probability of an edge is $p$ inside a group and $q$ between groups.
**Exact recovery** means that a labeling agrees with the planted partition,
or with its global flip, with probability tending to one.

* **11. Exact recovery.** For fixed $a,b>0$ in
  $p=a\log n/n$, $q=b\log n/n$, exact recovery is possible, and
  achievable in polynomial time, if and only if
  $$(\sqrt a-\sqrt b)^2\ge2.$$
  The equality case is included for strictly positive $a,b$.
  With $b=0$ and $a>0$, recovery instead requires $a>2$;
  the equality case has a connectivity obstruction. Thus the boundary
  cannot be described by a single strict inequality for all parameters.

**Weak recovery** means that a labeling, after the better global sign flip,
has correlation with the planted partition bounded away from zero with
probability tending to one.
**Consistent distinction** from an Erdős–Rényi model means the existence
of graph tests whose two error probabilities tend to zero. Contiguity
is a comparison of sequences of laws that can preclude such distinction;
it is not itself the definition of a recovery task.

* **12. Kesten–Stigum threshold.** For fixed $a,b>0$ in the
  constant-degree regime $p=a/n$, $q=b/n$, weak recovery is possible
  if and only if $(a-b)^2>2(a+b)$, and is achievable efficiently above
  that threshold. Strictly below it, the graph law is mutually contiguous
  to the corresponding Erdős–Rényi law, so consistent distinction is
  impossible. Weak recovery is impossible also at equality. The
  two-group result does not extend unchanged to arbitrarily many groups.

A **graphon** is a symmetric measurable function
$W:[0,1]^2\to[0,1]$. The graphon model draws latent variables
$U_i$ independently from the uniform law on $[0,1]$ and, conditionally on
the latent variables, includes each edge $\{i,j\}$ independently with
probability $W(U_i,U_j)$.

* **13. Aldous–Hoover theorem for graphs.** A simple undirected random
  graph on the positive integers whose law is invariant under finite
  vertex permutations is a mixture of graphon models. Two graphons
  induce the same random-graph law precisely when they are weakly
  isomorphic: they have equal pullbacks almost everywhere by suitable
  measure-preserving maps from a common atomless probability space.
  One need not be obtained from the other by a single invertible
  measure-preserving relabeling of $[0,1]$. The sequence analogue is
  de Finetti's theorem, CKMA SYNOPSIS06, item 55.

The **one-dimensional Weisfeiler–Leman algorithm** colors vertices by
iterating the multiset of colors in the neighborhood. A **message-passing
network** updates each vertex feature from the multiset, or the sum, of the
features of its neighbors.

* **14. Weisfeiler–Leman bound.** A message-passing network with shared
  updates and permutation-invariant neighborhood aggregation cannot
  distinguish initially equally featured graphs that one-dimensional
  Weisfeiler–Leman refinement does not distinguish. At depth $L$ the
  analogous comparison uses $L$ refinement rounds. With injective
  multiset aggregation, updates, and graph readout, the bound can be
  attained on the prescribed feature and multiset domain. Standard
  graph-isomorphism-network constructions use countable feature domains
  and bounded multiset sizes; unrestricted real-valued sum aggregation
  is not automatically injective.

### Symmetry and graph signal

* **31. Population eigenspaces of the block model.** For a balanced
  two-group model with label vector $s\in\{-1,1\}^n$ and $1^\top s=0$,
  the conditional adjacency expectation is
  $$\mathbb E[A\mid s]=\tfrac{p+q}{2}11^\top
  +\tfrac{p-q}{2}ss^\top-pI.$$
  Its eigenvectors $1$ and $s$ have eigenvalues
  $n(p+q)/2-p$ and $n(p-q)/2-p$, respectively; every orthogonal
  direction has eigenvalue $-p$. This identifies the population signal.
  Consistent empirical eigenvector recovery additionally requires
  noise and spectral-gap control. In sparse graphs, population
  separation alone does not make the unregularized adjacency method
  attain the thresholds of items 11 and 12.

* **32. Permutation equivariance.** For a shared message-passing map
  $F$ with permutation-invariant neighborhood aggregation and a vertex
  permutation matrix $P$,
  $$F(PAP^\top,PX)=PF(A,X).$$
  A permutation-invariant pooling of the resulting node features is
  a graph invariant. Equivariance is a constraint on relabeling, while
  the Weisfeiler–Leman theorem of item 14 bounds distinguishing power;
  one does not imply that the other is maximal.

<a id="synopsis-113d"></a>

## 113D. Bandits and Reinforcement Learning

A **stochastic bandit** has $K$ arms with reward laws $\nu_1,\ldots,\nu_K$
in a one-parameter exponential family. Write $\Delta_k$ for the gap between
the mean of arm $k$ and the optimal mean, and write
$\mathop{\mathrm{kl}}(\nu_k,\nu^\star)$ for the Kullback–Leibler divergence
between the reward law of arm $k$ and the optimal reward law.
Assume a regular one-parameter family with a continuous strictly increasing
mean parameter, a unique optimal arm, and optimal mean in the interior
of the mean domain. The
**regret** after $n$ plays is the expected difference between $n$ times the
optimal mean and the sum of the observed rewards.

* **15. Lai–Robbins lower bound.** For a uniformly efficient policy,
  meaning regret $o(n^\alpha)$ at every parameter configuration for every
  $\alpha>0$, the regular exponential-family bandit satisfies
  $$\liminf_{n\to\infty}\frac{\mathop{\mathrm{regret}}(n)}{\log n}
  \ge\sum_{k:\Delta_k>0}\frac{\Delta_k}
  {\mathop{\mathrm{kl}}(\nu_k,\nu^\star)}.$$
  More generally the denominator is the infimum divergence from $\nu_k$
  to an admissible arm law with mean strictly greater than the optimal
  mean. In the stated regular family, interiority and continuity reduce
  that infimum to the displayed divergence.

* **16. Upper confidence bounds.** For independent reward streams
  supported on $[0,1]$, the UCB1 policy, initialized by sampling each arm,
  has expected regret
  $$O\left(\sum_{k:\Delta_k>0}\frac{\log n}{\Delta_k}
  +\sum_{k:\Delta_k>0}\Delta_k\right).$$
  For fixed positive gaps this gives logarithmic growth. It matches the
  logarithmic order of item 15 in applicable exponential-family models,
  rather than its exact leading divergence constant.

* **17. Thompson sampling and the Gittins index.** For Bernoulli arms
  with means in $(0,1)$ and independent beta priors with positive
  parameters, Thompson sampling attains the asymptotic regret constant
  of item 15. Extensions require specified likelihood and prior
  regularity. For a Bayesian bandit with independent arms, each arm's
  state frozen when unplayed, and a common geometric discount factor,
  a Gittins index policy maximizes expected discounted reward. The
  index theorem concerns discounted Bayesian optimality, a different
  criterion from asymptotic frequentist regret.

* **18. Adversarial bandits.** For an oblivious sequence of losses
  in $[0,1]$ on $K\ge2$ arms, Exp3 with a horizon-tuned exploration
  parameter has expected regret $O(\sqrt{KT\log K})$ against the best
  fixed arm in hindsight. Only the selected loss is observed; importance
  weighting estimates the other arms' losses without bias.
  The full-information comparator is SYNOPSIS107, item 11.

Consider a finite Markov decision process with nonempty finite action
sets, discount $\gamma\in(0,1)$, and bounded rewards. The
**Bellman optimality operator** on action-value functions is
$$(TQ)(s,a)
=\mathbb E\Bigl[R+\gamma\max_{a'}Q(S',a')\Bigm| S=s,\,A=a\Bigr].$$

* **19. Contraction of the Bellman operator.** The operator $T$ is a
  $\gamma$-contraction of the supremum norm. It has a unique fixed point
  $Q^\star$. Every policy that is greedy for $Q^\star$ is optimal, and
  value iteration converges to $Q^\star$ geometrically with ratio $\gamma$.

On a finite state-action space the **tabular $Q$-learning** update replaces
$Q(s,a)$ by
$(1-\alpha)Q(s,a)+\alpha\bigl(r+\gamma\max_{a'}Q(s',a')\bigr)$ when $(s,a)$
is visited and a reward $r$ and a next state $s'$ are observed.

* **20. Convergence of $Q$-learning.** In the finite discounted model,
  assume each observed transition and reward has the specified conditional
  Markov law, and every state-action pair is visited infinitely often.
  For its own update sequence, require $0\le\alpha_t(s,a)\le1$,
  $\sum_t\alpha_t(s,a)=\infty$, and
  $\sum_t\alpha_t(s,a)^2<\infty$. Then $Q_t\to Q^\star$ almost surely.
  The infinite-visitation and step-size conditions apply to the actual
  visits to each pair, rather than merely to a global time sequence.

### Policy evaluation and policy-dependent distributions

For a policy $\pi$ in the finite discounted model, let $P_\pi$ and
$r_\pi$ be its transition matrix and expected one-step reward vector.

* **33. Policy evaluation and improvement.** The policy value is
  $$V^\pi=(I-\gamma P_\pi)^{-1}r_\pi
  =\sum_{t\ge0}\gamma^tP_\pi^t r_\pi.$$
  If $\pi'$ selects maximizing actions for
  $r(s,a)+\gamma\sum_{s'}P(s'\mid s,a)V^\pi(s')$, then
  $V^{\pi'}\ge V^\pi$ at every state. Policy iteration with a tie rule
  retaining current maximizing actions terminates after finitely many
  strict policy improvements at an optimal deterministic policy.

Fix an initial distribution $\mu$ and write
$J(\pi)=\mathbb E_{\mu,\pi}\sum_{t\ge0}\gamma^tR_t$.
The normalized **discounted occupancy measure** is
$d_\mu^\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\mathop{\mathrm{Law}}_{\mu,\pi}(S_t)$.
The **advantage** is $A^\pi(s,a)=Q^\pi(s,a)-V^\pi(s)$.

* **34. Performance difference identity.** For any two policies,
  $$J(\pi')-J(\pi)=\frac1{1-\gamma}
  \mathbb E_{S\sim d_\mu^{\pi'},\,A\sim\pi'(\cdot\mid S)}
  [A^\pi(S,A)].$$
  The state distribution on the right is that of the new policy.
  Replacing it by an old-policy empirical distribution without a
  justified approximation or reweighting changes the identity.

* **35. Policy gradient.** For a differentiable policy family with
  strictly positive action probabilities and parameter-independent
  transitions, rewards, and initial distribution,
  $$\nabla_\theta J(\pi_\theta)
  =\frac1{1-\gamma}\mathbb E_{d_\mu^{\pi_\theta},\pi_\theta}
  [\nabla_\theta\log\pi_\theta(A\mid S)Q^{\pi_\theta}(S,A)].$$
  Any action-independent baseline $b(S)$ may be subtracted from $Q$
  without changing this expectation. Finite state and action spaces,
  bounded rewards, and local differentiability justify the
  discounted differentiation. Variance and bias of a fitted critic
  are additional questions.

<a id="synopsis-113e"></a>

## 113E. Privacy, Fairness, and Distribution Shift

Data sets are **neighboring** when one is obtained from the other by
changing a single record. A mechanism $M$ is **$\varepsilon$-differentially
private** when
$P(M(D)\in A)\le e^\varepsilon P(M(D')\in A)$ for every measurable $A$ and
every neighboring pair. It is **$(\varepsilon,\delta)$-differentially
private** when the same comparison holds with an additive $\delta$ on the
right-hand side. The **$\ell^1$ sensitivity** of a query
$f$ is the supremum of $\|f(D)-f(D')\|_1$ over neighboring pairs.

* **21. Laplace mechanism.** If $f$ takes values in $\mathbb R^k$ and has
  $\ell^1$ sensitivity $\Delta>0$, the mechanism that adds an independent
  $\mathop{\mathrm{Lap}}(\Delta/\varepsilon)$ random variable to each
  coordinate is $\varepsilon$-differentially private. The density of
  $\mathop{\mathrm{Lap}}(b)$ on the line is $(1/(2b))e^{-|t|/b}$, so
  $b=\Delta/\varepsilon$ for $\Delta>0$ and $\varepsilon>0$.
  A zero-sensitivity query can be released directly. This is
  Theorem 3.6 of Dwork and Roth.

* **22. Composition.** The adaptive composition of $k$ mechanisms that are
  $(\varepsilon_i,\delta_i)$-differentially private is
  $\bigl(\sum_i\varepsilon_i,\sum_i\delta_i\bigr)$-differentially private.
  If each mechanism is $(\varepsilon,\delta)$-differentially private, then
  for every $\delta'\in(0,1)$ the composition is $(\varepsilon',k\delta+\delta')$-differentially
  private with
  $$\varepsilon'
  =\sqrt{2k\log(1/\delta')}\,\varepsilon
  +k\varepsilon(e^\varepsilon-1).$$
  These are Theorem 3.16 and Theorem 3.20 of Dwork and Roth.

* **23. Private mean estimation.** For independent observations
  supported on $[-1,1]$ and $0<\varepsilon\le1$, the minimax squared
  error under noninteractive $\varepsilon$-local differential privacy is
  of order $\min\{1,1/(n\varepsilon^2)\}$. Here each individual's
  release kernel must obey the privacy inequality for every pair of
  possible input values. Under central pure $\varepsilon$-privacy,
  where a mechanism sees the whole sample, the minimax error is of order
  $\min\{1,n^{-1}+(n\varepsilon)^{-2}\}$.
  Adding Laplace noise to the bounded sample mean attains the central
  order. Boundedness of the mean alone, without controlling the
  observation laws, does not justify these uniform rates.

A score $S$ satisfies **separation**, or equalized odds, when
$S\perp A\mid Y$. It satisfies **sufficiency** when $Y\perp A\mid S$.
For $S\in[0,1]$, calibration within groups is the stronger numerical
condition $P(Y=1\mid S,A)=S$ almost surely, which implies sufficiency.

* **24. Incompatibility of calibration and equalized odds.** Let $Y,A$
  be binary, with $P(Y=y,A=a)>0$ for all four cells and unequal group
  base rates. If a score satisfies both separation and sufficiency,
  it must determine $Y$ almost surely. Thus a score leaving unresolved
  label uncertainty cannot satisfy both conditions; perfect prediction
  is an exception. In particular, unequal base rates rule out simultaneous
  within-group calibration and separation for an imperfect score.
  Group-dependent randomized thresholding can give a released binary
  prediction equalized odds, possibly at substantial cost in accuracy.

Let $\mathcal H$ be a class of binary classifiers. The
**$\mathcal H\Delta\mathcal H$-divergence** is
$d_{\mathcal H\Delta\mathcal H}(P,Q)
=2\sup_{h,h'\in\mathcal H}|P(h\ne h')-Q(h\ne h')|$.
It is twice the integral probability metric of
[SYNOPSIS111](SYNOPSIS111.md) for these disagreement indicators.

* **25. Domain adaptation and covariate shift.** For binary
  classification and every $h\in\mathcal H$,
  $$R_T(h)\le R_S(h)+\tfrac12d_{\mathcal H\Delta\mathcal H}(P_S^X,P_T^X)
  +\inf_{g\in\mathcal H}(R_S(g)+R_T(g)).$$
  Under covariate shift, the conditional response law given $X$ is
  unchanged. If $P_T^X\ll P_S^X$ and $w=dP_T^X/dP_S^X$, then for
  an integrable loss $R_T(f)=\mathbb E_S[w(X)L(Y,f(X))]$.
  This identifies target risk; accuracy of its weighted empirical
  estimate also depends on moments of the density ratio.

### Privacy mechanisms and weighted inference

* **36. Post-processing and groups.** Any measurable randomized
  post-processing of an $(\varepsilon,\delta)$-private release, using
  only the release and fresh randomness, is again
  $(\varepsilon,\delta)$-private. For pure privacy, if datasets differ
  in at most $k$ records, repeated application of the neighboring-data
  inequality gives a factor $e^{k\varepsilon}$. These statements require
  no independence between the output coordinates.

* **37. Gaussian mechanism.** Let a vector query have Euclidean
  sensitivity $\Delta_2$. For $0<\varepsilon<1$, $0<\delta<1$,
  and $c>0$ with $c^2>2\log(1.25/\delta)$, adding independent
  $N(0,\sigma^2)$ coordinates with $\sigma\ge c\Delta_2/\varepsilon$
  is $(\varepsilon,\delta)$-differentially private. The norm used
  for sensitivity is part of the theorem; the Laplace mechanism of
  item 21 instead uses $\ell^1$ sensitivity.

* **38. Exponential mechanism.** For a fixed finite output set
  $\mathcal R$, let a utility $u(D,r)$ have sensitivity $\Delta u>0$
  uniformly over $r$. Drawing an output with probability proportional
  to $\exp(\varepsilon u(D,r)/(2\Delta u))$ is
  $\varepsilon$-differentially private. With probability at least
  $1-\eta$, the released utility is within
  $$\frac{2\Delta u}{\varepsilon}
  (\log|\mathcal R|+\log(1/\eta))$$
  of the maximum. The output set must not itself reveal the data.

* **39. Randomized response and a private mean.** For $\varepsilon>0$, put
  $\rho_\varepsilon=(e^\varepsilon-1)/(e^\varepsilon+1)$.
  For an individual input $x\in[-1,1]$, release $Z\in\{-1,1\}$ with
  $$P(Z=1\mid x)=\frac{1+\rho_\varepsilon x}{2}.$$
  This is $\varepsilon$-locally private and satisfies
  $\mathbb E[Z\mid x]=\rho_\varepsilon x$. For independent individuals
  and independent randomization, $\sum_iZ_i/(n\rho_\varepsilon)$ is
  unbiased for the population mean, with variance at most
  $1/(n\rho_\varepsilon^2)$. Clipping to $[-1,1]$ cannot increase
  squared error and gives the order in item 23 for $0<\varepsilon\le1$.

* **40. Accuracy under bounded importance weights.** Under covariate
  shift, suppose the known density ratio satisfies $0\le w\le B$,
  and the loss is in $[0,1]$. For a fixed predictor, or conditionally
  on independent training data, the weighted mean of $n$ independent
  source validation losses is unbiased for target risk and has
  variance at most $B/n$, since $\mathbb E_Sw=1$.
  A Bernstein bound gives, with probability at least $1-\delta$,
  $$|\hat R_T-R_T|\le
  \sqrt{\frac{2B\log(2/\delta)}n}
  +\frac{2B\log(2/\delta)}{3n}.$$
  Estimating the ratio or selecting the predictor on those same
  validation observations requires further error control.

## Reference guide

### Correspondence with the subdivisions

- **[113A](#synopsis-113a)**: Breiman, Friedman, Olshen, and Stone carry
  cost-complexity pruning. Pollard carries consistency of $k$-means.
  Wainwright and Jordan carry the Bethe free energy and belief propagation.
  Scornet, Biau, and Vert carry consistency of random forests in additive
  models.
- **[113B](#synopsis-113b)**: Cybenko, Hornik, Stinchcombe, and White, and
  Leshno, Lin, Pinkus, and Schocken carry universal approximation. Barron
  carries the dimension-free one-hidden-layer rate. Schmidt-Hieber carries
  compositional rates for deep ReLU networks. Jacot, Gabriel, and Hongler
  carry the neural tangent kernel. Hastie, Montanari, Rosset, and Tibshirani
  carry ridgeless interpolation. Goodfellow and coauthors carry the
  adversarial equilibrium.
- **[113C](#synopsis-113c)**: Abbe's survey carries the stochastic block model
  thresholds. Lovász carries graphons. Kolaczyk and Newman carry the
  statistical and probabilistic background on networks. Xu, Hu, Leskovec, and
  Jegelka carry the Weisfeiler–Leman comparison for message-passing networks.
- **[113D](#synopsis-113d)**: Lai and Robbins carry the asymptotic lower
  bound. Auer, Cesa-Bianchi, and Fischer carry UCB1 and Exp3. Puterman, and
  Bertsekas and Tsitsiklis, carry Markov decision processes and the
  convergence of $Q$-learning. Gittins carries the index theorem.
- **[113E](#synopsis-113e)**: Dwork and Roth carry differential privacy, the
  Laplace mechanism, and composition. Barocas, Hardt, and Narayanan carry
  the fairness definitions and the incompatibility and post-processing
  statements. Ben-David, Blitzer, Crammer, and Pereira carry the
  $\mathcal H\Delta\mathcal H$ bound. Shimodaira carries covariate-shift
  reweighting.

### Source comparisons and local copies

Wainwright–Jordan's tree and Bethe variational developments were consulted
for items 4 and 28. Their tree exactness does not imply convergence or
global optimality of loopy belief propagation. The corrected boosting
statement is the squared-error line-search identity; the forest statement
uses independent response estimation and locality, not honesty alone.
Scornet–Biau–Vert's response-adaptive theorem is a specialized result,
not a general corollary of the shrinking-cell argument.

The local Grohs–Kutyniok collection, Chapter 1, was read for Theorem 1.27
on Barron approximation and the tangent-kernel discussion around
equations (1.21)–(1.23). Item 7 specifies the statistical compositional
class and effective smoothness. Item 9 now gives finite-sample expected
Gaussian-design risks and assumes a limiting signal norm; item 10 permits
boundary discriminator values when claiming an attained maximum.
Bishop–Bishop supplies the probabilistic output and Gaussian-conditioning
framework for the new prediction entries.

[Abbe's survey, Theorem 13 and its boundary discussion](https://jmlr.org/papers/v18/16-480.html),
was checked online for items 11–12. The exact-recovery equality case
differs for positive and zero between-group probabilities. For item 13,
[Janson's Theorem 8.6](https://arxiv.org/abs/1009.2376)
gives common measure-preserving pullbacks, not necessarily one invertible
relabeling. Message-passing injectivity is stated only on the domain for
which it is assumed or constructed.

Puterman and Bertsekas–Tsitsiklis supply discounted policy evaluation,
improvement, and the stochastic approximation framework. The finite-model
conditions are now explicit for Bellman contraction and $Q$-learning.
Items 34–35 record the occupancy and score identities for those models.
The bandit entries distinguish instance-dependent logarithmic regret,
its leading divergence constant, discounted Bayesian index optimality,
and the oblivious-adversary bound. Lattimore–Szepesvári, Sutton–Barto,
and the original bandit papers were not located as local full texts.

Dwork–Roth, Proposition 2.1 and Sections 3.2–3.5, was consulted for
post-processing, randomized response, the exponential mechanism, and
Theorem 3.22 on Gaussian noise. Item 23 now fixes bounded observations
and the privacy model; it no longer states a uniform minimax rate from
boundedness of the mean alone. The local-model comparison is in
[Duchi–Jordan–Wainwright](https://arxiv.org/abs/1604.02390).
The central bounded-model upper bound follows from the sample mean's
sensitivity; its lower bound already occurs in bounded two-point families.

Barocas–Hardt–Narayanan, the chapter on classification criteria, was read
for separation, sufficiency, and their incompatibility propositions.
Calibration is distinguished from sufficiency, and perfect prediction
is retained as an exception. Item 25 fixes the conventional factor two
in the disagreement divergence, and item 40 gives a separate variance
condition for weighted inference.

Hastie–Tibshirani–Friedman, Goodfellow–Bengio–Courville, Murphy,
Bishop's 2006 pattern-recognition book, and Lovász were not located in
the two reference directories. Bishop–Bishop's 2024 text is a different
local book and was consulted. Original online papers read for this review
are identified above; the lists below also retain other source copies
identified in the first pass.

Local texts directly consulted or identified for this selection:

- [Bishop and Bishop, *Deep Learning: Foundations and Concepts*](../lean-CKMA/References/BishopBishop2024DeepLearningFoundationsConcepts-Springer.pdf).
  Probabilistic prediction and the diffusion chapter were consulted.
- [Dwork and Roth, *The Algorithmic Foundations of Differential Privacy*](../lean-CKMA/References/DworkRoth2014AlgorithmicFoundationsDifferentialPrivacy-NowPublishers.FnTTCS9.pdf).
  Theorems 3.6, 3.16, and 3.20 were read.
- [Wainwright and Jordan, *Graphical Models, Exponential Families, and Variational Inference*](../lean-CKMA/References/WainwrightJordan2008GraphicalModelsExponentialFamiliesVariationalInference-NowPublishers.FnTML1.pdf).
- [Breiman, Friedman, Olshen, and Stone, *Classification and Regression Trees*](../lean-CKMA/References/BreimanFriedmanOlshenStone1984ClassificationRegressionTrees-ChapmanHallCRC.pdf).
- [Koller and Friedman, *Probabilistic Graphical Models*](../lean-CKMA/References/KollerFriedman2009ProbabilisticGraphicalModelsPrinciplesTechniques-MITPress.ACML.pdf).
- [Anthony and Bartlett, *Neural Network Learning*](../lean-CKMA/References/AnthonyBartlett1999NeuralNetworkLearningTheoreticalFoundations-Cambridge.pdf).
- [Pinkus, *Ridge Functions*](../lean-CKMA/References/Pinkus2015RidgeFunctions-Cambridge.TractsMath205.pdf).
- [Grohs and Kutyniok, editors, *Mathematical Aspects of Deep Learning*](../lean-CKMA/References/GrohsKutyniokEds2023MathematicalAspectsDeepLearning-Cambridge.pdf).
- [Puterman, *Markov Decision Processes*](../lean-CKMA/References/Puterman1994rep2005MarkovDecisionProcessesDiscreteStochasticDynamicProgramming-WileySerProbStat.pdf).
- [Bertsekas and Tsitsiklis, *Neuro-Dynamic Programming*](../lean-CKMA/References/BertsekasTsitsiklis1996NeuroDynamicProgramming-AthenaScientific.pdf).
- [Meyn, *Control Systems and Reinforcement Learning*](../lean-CKMA/References/Meyn2022ControlSystemsReinforcementLearning-Cambridge.pdf).
- [Kolaczyk, *Statistical Analysis of Network Data*](../lean-CKMA/References/Kolaczyk2009StatisticalAnalysisNetworkDataMethodsModels-SpringerSSS.pdf).
- [Newman, *Networks*](../lean-CKMA/References/Newman2018Networks2ndEd-OxfordUP.pdf).
- [Barocas, Hardt, and Narayanan, *Fairness and Machine Learning*](../lean-CKMA/References/BarocasHardtNarayanan2022FairnessMachineLearningLimitationsOpportunities-AuthorManuscript.pdf).
- [Hardt and Recht, *Patterns, Predictions, and Actions*](../lean-CKMA/References/HardtRecht2023PatternsPredictionsActionsStoryMachineLearning-AuthorManuscript.pdf).
- [Blum, Hopcroft, and Kannan, *Foundations of Data Science*](../lean-CKMA/References/BlumHopcroftKannan2020FoundationsDataScience-Cambridge.pdf).
