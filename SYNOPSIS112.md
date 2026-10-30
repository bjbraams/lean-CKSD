# Synopsis: Mean-field limits and stochastic dynamics for data

Part of the [mathematical synopsis series](SYNOPSIS.md).
[Bibliographical scope and references](CKSD-bib.md#cks-112).

This synopsis follows Section 112. Subdivision 112A is Langevin sampling and
stochastic approximation. Subdivision 112B is interacting particle systems.
Subdivision 112C is score-based generation. The Wasserstein gradient flow of
free energy, the contraction of $\mathrm{EVI}$ flows, and entropic transport
are [CKMA SYNOPSIS39](../lean-CKMA/SYNOPSIS39.md), items 62, 59, and 90.
Girsanov's theorem and the Feynman–Kac formula are
[CKMA SYNOPSIS08](../lean-CKMA/SYNOPSIS08.md), items 29 and 36. Geometric
ergodicity is item 69 of that file. The Kalman filter is
[SYNOPSIS108](SYNOPSIS108.md), item 7. The Metropolis–Hastings algorithm and
the evidence lower bound are [SYNOPSIS105](SYNOPSIS105.md), items 12 and 15.
Mean-field games remain in CKMA Section 8.

Numbered definitions and results have stable identifiers. Additions take the
next free number and are placed beside related material; numbers need not
increase in reading order. Proofs are outside the scope of this synopsis.

<a id="synopsis-112a"></a>

## 112A. Langevin Dynamics, Sampling, and Gradient Flows

Let $V:\mathbb R^d\to\mathbb R$ be smooth and confining with
$\int e^{-V(x)}dx<\infty$, and let $\pi(dx)\propto e^{-V(x)}\,dx$.
Assume the stochastic dynamics are well posed and nonexplosive and the
integration-by-parts identities used below are justified.
The **overdamped Langevin diffusion** is
$$dX_t=-\nabla V(X_t)\,dt+\sqrt2\,dW_t.$$

* **1. Invariant measure and gradient-flow structure.** The probability
  $\pi$ is invariant for the diffusion. Its marginal flow is the
  $W_2$ gradient flow of $\rho\mapsto\int\rho\log\rho+\int V\,d\rho$, and
  therefore solves $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$.
  That identification is CKMA SYNOPSIS39, item 62.

* **2. Contraction under strong convexity.** If $\nabla^2V\ge mI$ for some
  $m>0$, then
  $$W_2(\mu_t,\pi)\le e^{-mt}W_2(\mu_0,\pi)$$
  for the law $\mu_t$ of $X_t$. The same convexity makes the relative
  entropy $m$-displacement-convex, so the $\mathrm{EVI}_m$ contraction of
  CKMA SYNOPSIS39, item 59, applies.

The **unadjusted Langevin algorithm** is the Euler–Maruyama discretization
$$X_{(n+1)h}=X_{nh}-h\nabla V(X_{nh})+\sqrt{2h}\,\xi_{n+1},$$
with $\xi_n$ standard normal. Write $\kappa=\beta/\alpha$ when
$\alpha I\preceq\nabla^2V\preceq\beta I$ and $\alpha>0$.

* **3. Iteration complexity of Langevin Monte Carlo.** Suppose
  $\alpha I\preceq\nabla^2V\preceq\beta I$, $\alpha>0$, and
  $\varepsilon\in(0,\sqrt d]$. A step size of order
  $\varepsilon^2/(\beta d)$ gives
  $\sqrt\alpha\,W_2(\hat\mu_{Nh},\pi)\le\varepsilon$ after
  $$N=O\left(\frac{\kappa d}{\varepsilon^2}
  \log\left(e+\frac{\alpha W_2^2(\hat\mu_0,\pi)}{\varepsilon^2}\right)\right)$$
  iterations. The mixture of marginal laws
  $\bar\mu=N^{-1}\sum_{j=N+1}^{2N}\hat\mu_{jh}$ satisfies
  $\sqrt{\mathop{\mathrm{KL}}(\bar\mu\|\pi)}\le\varepsilon$,
  with suitable constants. This is Chewi's Theorem 4.3.6.
  The mixture is the law of a randomly selected iterate, not the law
  of the arithmetic average of the iterates. A Metropolis–Hastings
  correction of the Euler proposal instead has invariant measure $\pi$.

Let $h:\mathbb R^p\to\mathbb R^p$ satisfy $h(\theta^\star)=0$, and let the
recursion be
$\theta_{n+1}=\theta_n-a_n\bigl(h(\theta_n)+M_{n+1}\bigr)$, where $M_{n+1}$
is a martingale difference.

* **4. Robbins–Monro convergence and averaging.** Suppose $h$ is
  globally Lipschitz and
  $(\theta-\theta^\star)\cdot h(\theta)\ge
  m\|\theta-\theta^\star\|^2$ for $m>0$. For positive steps with
  $\sum a_n=\infty$, $\sum a_n^2<\infty$, square-integrable initial
  state, and uniformly bounded conditional noise second moments,
  $\theta_n\to\theta^\star$ almost surely. More general ODE criteria
  require bounded iterates and an attracting limiting invariant set.
  For $a_n=n^{-\alpha}$, $1/2<\alpha<1$, suppose additionally that
  $h$ has a locally Lipschitz derivative, $A=Dh(\theta^\star)$ has
  eigenvalues with positive real part, conditional noise covariances
  tend to $S$, and the noise satisfies a uniform conditional
  $(2+\delta)$ moment bound. Then the averaged iterate satisfies
  $$\sqrt n(\bar\theta_n-\theta^\star)
  \Rightarrow N(0,A^{-1}SA^{-\top}).$$
  With the sign convention $\dot\theta=-h(\theta)$, it is $-A$
  that is Hurwitz. A nonnegative radial drift alone does not guarantee
  convergence to the specified root.

### Entropy and discretization bias

* **16. Entropy dissipation of Langevin flow.** For smooth positive
  densities with the needed integrability and boundary decay,
  $$\frac d{dt}\mathop{\mathrm{KL}}(\rho_t\|\pi)
  =-\int\|\nabla\log(\rho_t/\pi)\|^2\rho_t\,dx.$$
  If $\pi$ satisfies the logarithmic Sobolev inequality
  $\mathop{\mathrm{KL}}(\rho\|\pi)\le I(\rho\|\pi)/(2m)$,
  then KL decays at least as $e^{-2mt}$. Strong convexity
  $\nabla^2V\ge mI$ is a sufficient condition. Entropy dissipation
  measures distributional error, whereas item 2 controls $W_2$.

* **17. Exact Gaussian discretization bias.** For $V(x)=x^\top Ax/2$,
  $A>0$, the diffusion has invariant law $N(0,A^{-1})$.
  The unadjusted chain is stable for $0<h<2/\lambda_{\max}(A)$
  and has invariant covariance
  $$\Sigma_h=(A-\tfrac h2A^2)^{-1}.$$
  This follows from the discrete covariance equation
  $\Sigma_h=(I-hA)\Sigma_h(I-hA)+2hI$. At a fixed positive step,
  running the chain longer does not remove this bias. The example
  distinguishes time-discretization error from finite-time mixing error.

<a id="synopsis-112b"></a>

## 112B. Particle Methods, Data Assimilation, and Training Dynamics

Let $b(x,\mu)$ be a Lipschitz drift on $\mathbb R^d\times\mathcal P_1$.
The **McKean–Vlasov equation** is the law of
$d\bar X_t=b(\bar X_t,\mathop{\mathrm{Law}}(\bar X_t))\,dt+dW_t$. The
$N$-particle system uses the same drift evaluated at the empirical measure
of the $N$ particles.

* **5. Propagation of chaos.** Assume a drift globally Lipschitz in
  position and in $W_1$ of the measure, independent Brownian drivers,
  and independent identically distributed initial states with finite
  second moment, independent of those drivers. The limiting equation
  and particle systems are well posed. On every fixed finite time
  interval, the joint path law of any fixed $k$ particles converges to
  the $k$-fold product of the McKean–Vlasov path law as $N\to\infty$.
  The initial independence can be replaced by an appropriate chaotic
  initial sequence. Fixed-time chaos alone is not a statement uniform
  over arbitrarily long time horizons.

In a linear-Gaussian state-space model, the **ensemble Kalman** update
replaces the forecast covariance in the Kalman gain by the covariance of a
finite ensemble.

* **6. Ensemble Kalman limit.** In a linear-Gaussian model with
  independent forecast noises and independent Gaussian initial ensemble,
  the perturbed-observation update
  $$X_i^a=X_i^f+K_N(y+\eta_i-HX_i^f),\qquad
  \eta_i\sim N(0,R),$$
  with $K_N=C_NH^\top(HC_NH^\top+R)^{-1}$ and $R>0$, converges at
  each fixed assimilation time to the Kalman analysis law as $N\to\infty$.
  A properly constructed square-root update has the same limiting
  mean and covariance. Updating all forecast particles against the same
  unperturbed observation without a covariance correction does not have
  the correct analysis covariance. For nonlinear models, an infinite
  ensemble does not in general give the exact Bayesian filter.

Consider a two-layer network whose parameters are $N$ particles and whose
prediction at a feature $x$ is an average of ridge functions of those
particles. Under a $1/N$ scaling of the output weights, gradient descent on
the empirical risk induces a flow on the empirical measure of the particles.

* **7. Mean-field training.** Write
  $f_\rho(x)=\int\phi(x,\theta)\,\rho(d\theta)$ and
  $\mathcal R(\rho)=\mathbb E L(Y,f_\rho(X))$ for a fixed data law.
  For $N$ particles and the time scaling
  $\dot\theta_i=-N\nabla_{\theta_i}\mathcal R(\rho_N)$,
  assume smooth bounded Lipschitz interaction derivatives, compactly
  supported independent initialization, and well-posed characteristic
  flows on the time interval considered. Then $\rho_N$ converges on
  each finite time interval to
  $$\partial_t\rho=\nabla\cdot
  \left(\rho\nabla_\theta\frac{\delta\mathcal R}{\delta\rho}\right).$$
  An empirical data law gives empirical risk in this limit; a population
  law gives population risk. Global convergence of the risk is a separate
  theorem requiring further assumptions. Positive homogeneity and an
  initialization with full support alone do not establish it.

**Stein variational gradient descent** evaluates a kernel velocity at
particle locations. Its variational derivation differentiates the
Kullback–Leibler divergence of a smooth density under transport;
the KL divergence of a finite atomic measure from a positive continuous
target is infinite and is not the differentiable objective.

* **8. Stein variational flow.** For a smooth density $\rho$, a smooth
  positive target density $\pi$, and a differentiable scalar kernel $k$,
  with integrable terms and vanishing integration-by-parts boundary terms,
  the RKHS descent velocity is
  $$v_\rho(x)=\int[k(y,x)\nabla\log\pi(y)+\nabla_y k(y,x)]\rho(y)\,dy
  =\int k(y,x)(\nabla\log\pi(y)-\nabla\log\rho(y))\rho(y)\,dy.$$
  Along $\partial_t\rho=-\nabla\cdot(\rho v_\rho)$,
  $$\frac d{dt}\mathop{\mathrm{KL}}(\rho\|\pi)
  =-\|v_\rho\|_{\mathcal H^d}^2.$$
  This is a kernel-dependent transport geometry; it is not in general
  the ordinary $W_2$ gradient flow of KL. Replacing the integrals by
  particle sums defines the finite-particle update without assigning
  finite KL to the empirical measure.

A **particle filter** approximates the filter of a hidden Markov model by a
weighted system of particles, resampled according to the incremental
likelihood weights. The underlying unnormalized measures are the
Feynman–Kac measures of CKMA SYNOPSIS08, item 36.

* **9. Consistency of the particle filter.** If the observation potentials
  are bounded and bounded away from zero, then at each fixed time the
  particle approximation of the filter converges in probability to the true
  filter as the number of particles tends to infinity.

### Quantitative chaos and nonlinear filtering

* **18. A quantitative interaction model.** Suppose
  $b(x,\mu)=b_0(x)+\int K(x,y)\,\mu(dy)$, where $b_0$ is globally
  Lipschitz and $K$ is bounded and globally Lipschitz. Couple the
  particles with independent nonlinear copies using the same initial
  values and Brownian motions. For every finite $T$,
  $$\mathbb E\sup_{t\le T}\|X_t^{i,N}-\bar X_t^i\|^2\le C_T/N.$$
  The bound follows from the variance of an empirical interaction and
  Grönwall's inequality. Its constant can grow with $T$; a uniform-time
  bound needs additional dissipativity or contractivity.

* **19. Prediction and Bayesian correction.** For a hidden Markov model,
  let $M_t$ be the state transition kernel and
  $G_t(x)=p(y_t\mid x)>0$ the likelihood of the observed datum.
  The exact filtering probabilities obey
  $$\eta_t^- =\eta_{t-1}M_t,\qquad
  \eta_t(f)=\frac{\eta_t^-(G_tf)}{\eta_t^-(G_t)}.$$
  The data likelihood satisfies
  $Z_t=Z_{t-1}\eta_t^-(G_t)$, $Z_0=1$.
  For nonlinear or non-Gaussian models this recursion acts on entire
  measures, even when a Gaussian approximation only tracks moments.

* **20. Unbiased particle likelihood.** In a bootstrap particle filter
  with conditionally unbiased resampling, let $X_t^{i,-}$ be the
  predicted particles and set
  $$\hat Z_t=\prod_{s=1}^t
  \left(\frac1N\sum_{i=1}^NG_s(X_s^{i,-})\right).$$
  Then $\mathbb E\hat Z_t=Z_t$, even though the normalized particle
  estimate of $\eta_t(f)$ is generally biased at finite $N$.
  With bounded positive potentials bounded away from zero and fixed
  $t$, its mean squared error for bounded $f$ is at most
  $C_t\|f\|_\infty^2/N$. Uniformity in $t$ requires additional mixing
  assumptions. The likelihood statement conditions on the observed data
  and averages over the particle system's randomness.

<a id="synopsis-112c"></a>

## 112C. Score Matching, Diffusion Generative Models, and Schrödinger Bridges

Let the forward diffusion on $[0,T]$ be
$$dX_t=f(t,X_t)\,dt+g(t)\,dW_t,$$
with $g(t)$ invertible, and write $p_t$ for the law of $X_t$. The **time
reversal** is $Y_t=X_{T-t}$.

* **10. Anderson's time reversal and the probability-flow equation.** Under
  smoothness, nonexplosion, ellipticity, and integrability hypotheses
  for time reversal, with smooth positive marginal densities and
  well-posed reverse dynamics,
  $$
  dY_t=\Bigl(-f(T-t,Y_t)+g(T-t)g(T-t)^\top\nabla\log p_{T-t}(Y_t)\Bigr)dt
  +g(T-t)\,d\bar W_t.
  $$
  The ordinary differential equation with the same drift except for a factor
  $\tfrac12$ on the score correction has, at each time, the same marginal
  law as $Y_t$.

For a smooth positive density $q_\theta$ with the same support as a data
density $p$, the **Hyvärinen objective** is
$$\int\Bigl(\tfrac12\|\nabla\log q_\theta\|^2+\Delta\log q_\theta\Bigr)\,dp.$$

* **11. Score matching.** If the boundary terms from integration by parts
  vanish, the Hyvärinen objective equals
  $\tfrac12\int\|\nabla\log q_\theta-\nabla\log p\|^2\,dp$ up to a constant
  free of $\theta$. If $Y=X+\sigma\varepsilon$ with $\varepsilon$ standard
  normal and independent of $X$, the regression target $-\varepsilon/\sigma=-(Y-X)/\sigma^2$
  has conditional expectation $\nabla\log p_\sigma(Y)$, where $p_\sigma$ is
  the law of $Y$. The population minimizer of the corresponding least-squares
  objective is therefore the score of the smoothed density.

A **diffusion generative model** runs a forward noising process from the
data law toward a simple reference law, estimates the score along that
process, and generates a sample by the reverse equation of item 10, or by
its probability-flow equation, with the estimated score in place of
$\nabla\log p_t$.

* **12. Generation by a learned reversal.** Suppose the learned reverse
  SDE is initialized from the correct terminal law $p_T$, or from laws
  $\eta$ with $\mathop{\mathrm{KL}}(p_T\|\eta)\to0$. If the
  time-integrated, diffusion-weighted
  score error in item 15 tends to zero and the change-of-measure
  hypotheses there hold, the endpoint laws converge in total variation
  to the endpoint law of the exact reversal. This conclusion concerns
  the continuous-time SDE. Numerical discretization and probability-flow
  ODEs require their own error controls. If the reversal is stopped at
  a positive noising time, its endpoint is the smoothed data law; this
  does not assert total-variation recovery of a singular data law.

Let $R$ be the path law of Brownian motion with a specified initial
probability, or another specified Markov reference. The **Schrödinger bridge** from $\mu_0$ to
$\mu_1$ is the path measure of minimum Kullback–Leibler divergence from $R$
among path measures with those endpoint marginals.

* **13. Schrödinger bridge.** Suppose a finite-entropy feasible path
  law exists. The bridge is unique and reduces to minimizing
  $\mathop{\mathrm{KL}}(\gamma\|R_{0T})$ over couplings of the prescribed
  endpoints. Given those endpoints its conditional path law is that of
  the reference bridge. For standard Brownian motion,
  $R_{0T}(dx,dy)=r_0(x)q_T(y-x)\,dx\,dy$ with
  $q_T(z)=(2\pi T)^{-d/2}e^{-\|z\|^2/(2T)}$.
  When the endpoint densities and their entropies permit this rewriting,
  the static problem is, up to marginal-only constants,
  $$\inf_{\gamma\in\Pi(\mu_0,\mu_T)}
  \left\{\int\frac{\|x-y\|^2}{2T}\,d\gamma
  +\mathop{\mathrm{KL}}(\gamma\|\mu_0\otimes\mu_T)\right\}.$$
  The reference initial law is part of the specification; unrestricted
  Wiener paths from a fixed point cannot realize a different initial
  marginal at finite relative entropy.

Let $(X_0,X_1)$ be a coupling of $\mu_0$ and $\mu_1$, and let
$v_t(x\mid x_0,x_1)$ be a conditional velocity whose flow carries $x_0$ to
$x_1$. **Flow matching** regresses a time-dependent vector field against
that conditional velocity.

* **14. Marginal velocity.** For differentiable conditional paths
  $X_t$ with square-integrable velocities, conditional expectation gives
  the population least-squares minimizer
  $$v_t(x)=\mathbb E[\dot X_t\mid X_t=x].$$
  The marginal law $\mu_t$ satisfies
  $\partial_t\mu_t+\nabla\cdot(\mu_t v_t)=0$ weakly, whenever
  differentiation under the expectation is justified. If this continuity
  equation is uniquely represented by a well-posed ODE flow, that flow
  carries $\mu_0$ to $\mu_1$. The conditional-expectation identity alone
  does not ensure a classical ODE exists at singular endpoints.

* **15. Score error and total variation.** Let $P$ be the exact reverse
  path law and $Q$ use an estimated score $s_t$, the same diffusion
  coefficient, and initial law $\eta$ at reverse time zero. Assume the
  Girsanov absolute-continuity and integrability conditions, including
  $p_T\ll\eta$. Then
  $$\mathop{\mathrm{KL}}(P\|Q)
  =\mathop{\mathrm{KL}}(p_T\|\eta)
  +\frac12\int_0^T\mathbb E_{p_t}
  \|g(t)^\top(s_t-\nabla\log p_t)\|^2\,dt.$$
  Marginalization cannot increase KL, and the endpoint total variation
  is at most $\sqrt{\mathop{\mathrm{KL}}(P\|Q)/2}$.
  The bound requires the weighted error integral, not just pointwise
  convergence at each time. Its dimension and horizon dependence comes
  through that integral and the initialization error; smooth marginal
  densities alone imply no uniform polynomial complexity bound.

### Gaussian noising, endpoint constraints, and interpolants

* **21. Tweedie's denoising identity.** Let $Y=X+\sigma\varepsilon$,
  $\sigma>0$, with independent standard Gaussian $\varepsilon$ and
  $X\in L^2$. For the positive smoothed density $p_\sigma$,
  $$\mathbb E[X\mid Y=y]=y+\sigma^2\nabla\log p_\sigma(y).$$
  Differentiating the Gaussian convolution also gives
  $$\mathop{\mathrm{Cov}}(X\mid Y=y)
  =\sigma^2I+\sigma^4\nabla^2\log p_\sigma(y).$$
  Thus squared-error denoising, noise prediction, and estimation of the
  smoothed score are linked by explicit scale factors, as in item 11.

* **22. Gaussian diffusion marginals.** For the forward chain
  $Z_t=\sqrt{1-\beta_t}Z_{t-1}+\sqrt{\beta_t}\xi_t$,
  with independent standard normal noises and $0<\beta_t<1$, put
  $\bar\alpha_t=\prod_{s=1}^t(1-\beta_s)$. Then
  $$Z_t\mid Z_0=x\sim
  N(\sqrt{\bar\alpha_t}x,(1-\bar\alpha_t)I).$$
  The population squared-error minimizer for predicting the aggregate
  standard normal noise $\varepsilon$ from $Z_t$ is
  $\mathbb E[\varepsilon\mid Z_t]$. Multiplying it by
  $-1/\sqrt{1-\bar\alpha_t}$ gives the marginal score at time $t$.
  The identity concerns the population optimum and does not by itself
  control the error of a fitted denoiser.

* **23. Endpoint potentials and entropy projection.** Under existence
  and dual-attainment assumptions for the Schrödinger problem, its path
  law has the form
  $$\frac{dP^*}{dR}=f(X_0)g(X_T).$$
  Strictly positive continuous reference kernels and positive bounded
  endpoint densities on compact state spaces are a useful sufficient
  setting. The factors enforce the two prescribed marginals and are
  determined up to reciprocal constants. For every feasible $Q$ with
  finite relevant entropies and integrable log potentials,
  $$\mathop{\mathrm{KL}}(Q\|R)
  =\mathop{\mathrm{KL}}(Q\|P^*)+
  \mathop{\mathrm{KL}}(P^*\|R).$$
  This entropy projection explains uniqueness and the reduction to
  endpoint coupling in item 13.

* **24. Straight interpolants and transport action.** For any coupling
  of square-integrable endpoints, put $X_t=(1-t)X_0+tX_1$ and
  $v_t(x)=\mathbb E[X_1-X_0\mid X_t=x]$. Then
  $$W_2^2(\mu_0,\mu_1)\le
  \int_0^1\mathbb E\|v_t(X_t)\|^2dt
  \le\mathbb E\|X_1-X_0\|^2.$$
  The right inequality is conditional Jensen; the left is the
  dynamic transport bound for the induced continuity equation.
  An optimal quadratic endpoint coupling gives displacement
  interpolation, CKMA SYNOPSIS39, item 48. An arbitrary coupling need
  not produce the optimal-transport path.

## Reference guide

### Correspondence with the subdivisions

- **[112A](#synopsis-112a)**: Pavliotis carries the Langevin diffusion.
  Chewi's manuscript carries non-asymptotic bounds for its discretization.
  Kushner and Yin, and Borkar, carry stochastic approximation and averaging.
  Ambrosio, Gigli, and Savaré carry the gradient-flow identification already
  numbered in CKMA SYNOPSIS39.
- **[112B](#synopsis-112b)**: Sznitman carries propagation of chaos. Carmona
  and Delarue carry mean-field games and interacting diffusions. Del Moral
  carries Feynman–Kac particle systems. Mei, Montanari, and Nguyen, and
  Chizat and Bach, carry the mean-field limit of two-layer networks.
- **[112C](#synopsis-112c)**: Hyvärinen carries score matching. Vincent
  carries denoising score matching. Song, and Ho, Jain, and Abbeel, carry
  diffusion generative models. Léonard, and Peyré and Cuturi, carry the
  Schrödinger bridge. Lipman, Chen, Ben-Hamu, Nickel, and Le carry flow
  matching.

### Source comparisons and local copies

Chewi's local 2026 manuscript, Theorem 4.3.6, was reread. Its entropy
guarantee is for a mixture of iterate laws, with square-root KL bounded by
$\varepsilon$; it is not a guarantee for the law of the arithmetic average.
The Gaussian covariance calculation in item 17 gives an exact example
of discretization bias. Pavliotis supplies the invariant-density and entropy
framework; Kushner–Yin and Borkar supply stochastic approximation. The
minus sign in the recursion makes positive real parts of $Dh$ the stable
case. Nonnegative radial drift without attraction was insufficient.

Law–Stuart–Zygalakis was found in `ReferencesSuppl`; Sections 4.2.3–4.2.4
were read for perturbed-observation and square-root ensemble updates.
The distinction from exact nonlinear filtering is explicit there.
Del Moral's 2013 volume treats Feynman–Kac measures, unbiased unnormalized
particle estimates, and particle normalizing constants. Items 19–20 use
fixed observations and average over particle randomness. Finite-time
propagation of chaos requires an initial independence or chaos hypothesis;
neither it nor a finite-time training limit implies a global convergence
or uniform-time theorem.

For item 8, [Liu and Wang's original paper](https://papers.neurips.cc/paper_files/paper/2016/hash/b3ba8f1bee1238a2f37603d90b58898d-Abstract.html)
was read for the transport derivative and kernel velocity. The smooth-law
variational calculation does not differentiate the infinite KL divergence
of an empirical atomic measure from a continuous target.

Bishop–Bishop, Chapter 20, especially Sections 20.2–20.3, was read for
Gaussian diffusion marginals, denoising scores, and reverse SDEs.
The noise target in item 11 is $-\varepsilon/\sigma$ when
$Y=X+\sigma\varepsilon$. Item 21 follows by differentiating that Gaussian
convolution. The endpoint error in item 15 is the Girsanov entropy
identity and marginal contraction; it includes initialization, weighted
time-integrated score error, and absolute continuity. No automatic
polynomial dimension bound is asserted.

Peyré–Cuturi's Schrödinger discussion distinguishes static endpoint
coupling from reference conditional bridges. Item 13 specifies the
Brownian noise normalization and initial reference law. The conditional
expectation in flow matching gives a continuity equation; a deterministic
ODE representation needs well-posedness. The straight-interpolant action
bound in item 24 is also a direct consequence of conditional Jensen and
CKMA SYNOPSIS39, items 48–49.

Evensen's book and the original papers of Song, Ho–Jain–Abbeel, and
Lipman and coauthors were not located locally. Their diffusion framework
is treated in the consulted Bishop–Bishop text. Del Moral's local book
is the 2013 volume, not the 2004 Feynman–Kac monograph.

Local texts directly consulted or identified for this selection:

- [Law, Stuart, and Zygalakis, *Data Assimilation: A Mathematical Introduction*](../lean-CKMA/ReferencesSuppl/LawStuartZygalakis2015DataAssimilationMathematicalIntroduction-Springer.TAM62.pdf).
  The two ensemble Kalman variants in Sections 4.2.3–4.2.4 were read.
- [Bishop and Bishop, *Deep Learning: Foundations and Concepts*](../lean-CKMA/References/BishopBishop2024DeepLearningFoundationsConcepts-Springer.pdf).
  Chapter 20 was consulted for diffusion and score models.
- [Chewi, *Log-Concave Sampling*](../lean-CKMA/References/Chewi2026LogConcaveSampling-AuthorManuscript.pdf).
  Theorem 4.3.6 was read.
- [Pavliotis, *Stochastic Processes and Applications*](../lean-CKMA/References/Pavliotis2014StochasticProcessesApplications-SpringerTAM.pdf).
- [Kushner and Yin, *Stochastic Approximation and Recursive Algorithms and Applications*](../lean-CKMA/References/KushnerYin2003StochasticApproximationRecursiveAlgorithmsApplications2ndEd-Springer.SMAP35.pdf).
- [Borkar, *Stochastic Approximation: A Dynamical Systems Viewpoint*](../lean-CKMA/References/Borkar2023StochasticApproximationDynamicalSystemsViewpoint2ndEd-SpringerHindustanTRIM48.pdf).
- [Ambrosio, Gigli, and Savaré, *Gradient Flows*](../lean-CKMA/References/AmbrosioGigliSavaré2008GradientFlowsMetricSpacesSpaceProbabilityMeasures2ndEd-Birkhäuser.LMETH.pdf).
- [Del Moral, *Mean Field Simulation for Monte Carlo Integration*](../lean-CKMA/References/DelMoral2013MeanFieldSimulationMonteCarloIntegration-ChapmanHallCRC.MSAP126.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. I](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications1FBSDEsControl-SpringerPTSM83.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. II](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications2CommonNoiseMasterEquations-SpringerPTSM84.pdf).
- [Peyré and Cuturi, *Computational Optimal Transport*](../lean-CKMA/References/PeyréCuturi2019ComputationalOptimalTransportApplicationsDataSciences-NowPublishers.FnTML11.pdf).
