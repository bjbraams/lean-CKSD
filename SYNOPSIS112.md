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
the evidence lower bound are [SYNOPSIS105](SYNOPSIS105.md), items 12 and 15,
and Hamiltonian Monte Carlo is item 35 of that file; discrete-time Markov chain
samplers stay there, while their continuous-time dynamics and discretizations
are here. Poincaré and logarithmic Sobolev inequalities, with the Bakry–Émery
criterion, are [CKMA SYNOPSIS14](../lean-CKMA/SYNOPSIS14.md), items 34–38 and
47–48. Mean-field games remain in CKMA Section 8.

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

### Variational time stepping and functional inequalities

Write $\mathcal F(\rho)=\int\rho\log\rho\,dx+\int V\rho\,dx$, which differs
from $\mathop{\mathrm{KL}}(\rho\|\pi)$ by a constant. For a time step
$\tau>0$ and a probability density $\rho_0$, the **JKO scheme** sets
$\rho_0^\tau=\rho_0$ and lets $\rho_{k+1}^\tau$ minimize
$$\rho\mapsto\frac1{2\tau}W_2^2(\rho,\rho_k^\tau)+\mathcal F(\rho)$$
over probability densities with finite second moment. Its piecewise-constant
interpolation is $\rho^\tau(t)=\rho_k^\tau$ for $k\tau\le t<(k+1)\tau$.

* **25. Jordan–Kinderlehrer–Otto theorem.** Let $V$ be smooth and
  nonnegative with $\|\nabla V\|\le C(V+1)$, and let $\rho_0$ have
  finite second moment and $\mathcal F(\rho_0)<\infty$. Then every step
  of the JKO scheme has a unique minimizer. As $\tau\downarrow0$,
  $\rho^\tau(t)$ converges weakly in $L^1$ for every $t\ge0$, and
  strongly in $L^1((0,T)\times\mathbb R^d)$ for every $T$, to the unique
  solution of $\partial_t\rho=\Delta\rho+\nabla\cdot(\rho\nabla V)$ with
  initial datum $\rho_0$. Each step is an implicit Euler step in $W_2$ for
  the relative entropy, so the law of the Langevin diffusion is obtained as
  a limit of entropy minimizations. Here $\pi$ need not be normalizable;
  the general metric version is CKMA SYNOPSIS39, items 57 and 61–62.

The **chi-squared divergence** is
$\chi^2(\mu\|\pi)=\mathop{\mathrm{Var}}_\pi(d\mu/d\pi)$ if $\mu\ll\pi$, and
$+\infty$ otherwise. The target $\pi$ satisfies a **Poincaré inequality**
with constant $C_P$ if $\mathop{\mathrm{Var}}_\pi f\le C_P\,\mathbb E_\pi\|\nabla f\|^2$
for all smooth $f$, and a **logarithmic Sobolev inequality** with constant
$C_{LS}$ if $\mathop{\mathrm{KL}}(\mu\|\pi)\le\tfrac{C_{LS}}2
\mathbb E_\mu\|\nabla\log(d\mu/d\pi)\|^2$ for all smooth positive $\mu$.
Item 16 is the case $C_{LS}=1/m$.

* **26. Convergence of the Langevin diffusion under functional
  inequalities.** Let $\mu_t$ be the law of $X_t$. The Poincaré
  inequality with constant $C_P$ holds if and only if
  $$\chi^2(\mu_t\|\pi)\le e^{-2t/C_P}\chi^2(\mu_0\|\pi)$$
  for every initial law. The logarithmic Sobolev inequality with constant
  $C_{LS}$ holds if and only if
  $\mathop{\mathrm{KL}}(\mu_t\|\pi)\le e^{-2t/C_{LS}}
  \mathop{\mathrm{KL}}(\mu_0\|\pi)$ for every initial law, and it then
  also gives
  $W_2^2(\mu_t,\pi)\le2C_{LS}e^{-2t/C_{LS}}\mathop{\mathrm{KL}}(\mu_0\|\pi)$
  by the Otto–Villani inequality, CKMA SYNOPSIS14, item 57. The logarithmic
  Sobolev inequality implies the Poincaré inequality with $C_P\le C_{LS}$.
  Neither requires convexity: if $V=V_0+\psi$ with $\nabla^2V_0\ge mI$,
  $m>0$, and $\psi$ bounded, then both hold with constant at most
  $e^{\sup\psi-\inf\psi}/m$, by CKMA SYNOPSIS14, items 38 and 48.
  For a point-mass or otherwise concentrated start, $\chi^2(\mu_0\|\pi)$
  typically grows exponentially in $d$, while
  $\mathop{\mathrm{KL}}(\mu_0\|\pi)$ grows only polynomially; this is why
  sampling bounds are usually stated under the logarithmic Sobolev
  inequality.

### Unadjusted, stochastic-gradient, and Metropolis-adjusted Langevin

Let $\hat\mu_{nh}$ denote the law of the $n$-th iterate of the unadjusted
Langevin algorithm above. The potential is **$\beta$-smooth** if $\nabla V$
is $\beta$-Lipschitz.

* **27. Langevin Monte Carlo under a logarithmic Sobolev inequality.**
  Suppose $\pi$ satisfies the logarithmic Sobolev inequality with
  constant $1/\alpha$ and $V$ is $\beta$-smooth; $V$ need not be convex.
  For $0<h\le1/(4\beta)$ and all $N$,
  $$\mathop{\mathrm{KL}}(\hat\mu_{Nh}\|\pi)\le
  e^{-\alpha Nh}\mathop{\mathrm{KL}}(\hat\mu_0\|\pi)
  +O\!\left(\frac{\beta^2dh}\alpha\right)$$
  (Vempala–Wibisono). With $\kappa=\beta/\alpha$ and a step of order
  $\varepsilon^2/(\beta\kappa d)$, one gets
  $\mathop{\mathrm{KL}}(\hat\mu_{Nh}\|\pi)\le\varepsilon^2$ after
  $N=O(\kappa^2d\varepsilon^{-2}\log(\mathop{\mathrm{KL}}(\hat\mu_0\|\pi)/\varepsilon^2))$
  iterations. If instead $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$
  and $h$ is small compared with $1/(\beta\kappa)$, a synchronous coupling
  gives
  $$W_2(\hat\mu_{Nh},\pi)\le e^{-\alpha Nh/2}W_2(\hat\mu_0,\pi)
  +O\!\left(\frac{\beta\sqrt{dh}}\alpha\right).$$
  In both bounds the second term is a bias that persists as
  $N\to\infty$ at fixed $h$, as in item 17.

A **stochastic gradient oracle** returns, at each query point $x$ and with
fresh randomness, a vector $\widehat{\nabla V}(x)$ with
$\mathbb E\widehat{\nabla V}(x)=\nabla V(x)$ and
$\mathbb E\|\widehat{\nabla V}(x)-\nabla V(x)\|^2\le\sigma^2$; a minibatch
gradient of a sum over data points is the typical case. **Stochastic
gradient Langevin dynamics** replaces $\nabla V$ by
$\widehat{\nabla V}$ in the unadjusted Langevin algorithm.

* **28. Stochastic gradient Langevin dynamics.** The one-step mean of the
  stochastic-gradient update equals that of the exact-gradient update, so
  the weak local error is unchanged; the strong local error acquires an
  additional term of order $\sigma h$. Under
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$, a step size of suitable
  order gives $\sqrt\alpha\,W_2(\hat\mu_{Nh},\pi)\le\varepsilon$ after
  $$N=\tilde O\!\left(\frac{\kappa^2d}{\varepsilon^2}
  +\frac{\sigma^2}{\alpha\varepsilon^2}\right)$$
  iterations. The second term is the strongly convex stochastic-gradient
  rate. At fixed step the gradient noise adds a further bias; the original
  proposal of Welling and Teh uses decreasing steps, as in stochastic
  approximation (item 4).

The **Metropolis-adjusted Langevin algorithm** (MALA) uses the
unadjusted step $y=x-h\nabla V(x)+\sqrt{2h}\,\xi$ as the proposal of the
Metropolis–Hastings algorithm of SYNOPSIS105, item 12, with proposal density
$q(x,y)\propto\exp(-\|y-x+h\nabla V(x)\|^2/(4h))$. Its kernel leaves $\pi$
invariant for every $h>0$, so it has no discretization bias. The random-walk
Metropolis algorithm uses $y=x+\sqrt{2h}\,\xi$ instead. A start $\mu_0$ is
**warm** if $\chi^2(\mu_0\|\pi)=O(1)$.

* **29. Mixing and scaling of Metropolis-adjusted Langevin.** Suppose
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and $\kappa=\beta/\alpha$.
  From a warm start and with suitably tuned $h$, MALA reaches total
  variation $\varepsilon$ after $\tilde O(\kappa d^{1/2}\mathop{\mathrm{polylog}}(1/\varepsilon))$
  iterations. From the cold start $N(x^\star,\beta^{-1}I)$, with $x^\star$
  the minimizer of $V$, it needs $\tilde O(\kappa d\mathop{\mathrm{polylog}}(1/\varepsilon))$
  iterations, as does random-walk Metropolis. The warm-start dimension
  dependence is sharp: for every $h$ there are such targets and warm starts
  requiring $\tilde\Omega(\kappa\sqrt d\log(1/\varepsilon))$ iterations.
  The dependence on $\varepsilon$ is polylogarithmic, in contrast with the
  polynomial dependence of items 3 and 27. In the older asymptotic theory,
  for product targets $\pi_d=f^{\otimes d}$ with smooth $\log f$ and a
  stationary start, random-walk proposals of variance $\ell^2/d$ give, after
  speeding up time by $d$, a Langevin diffusion limit for each coordinate,
  with efficiency maximized at asymptotic acceptance rate about $0.234$
  (Roberts–Gelman–Gilks). For MALA the corresponding step is
  $h=\ell^2d^{-1/3}$ and the optimal acceptance rate is about $0.574$
  (Roberts–Rosenthal). These scaling limits presuppose stationarity and
  product structure; they are not mixing-time bounds.

### Kinetic Langevin dynamics

The **underdamped**, or kinetic, **Langevin diffusion** with friction
$\gamma>0$ is
$$dX_t=P_t\,dt,\qquad dP_t=-\nabla V(X_t)\,dt-\gamma P_t\,dt+\sqrt{2\gamma}\,dW_t$$
on $\mathbb R^{2d}$. Hamiltonian Monte Carlo, which refreshes the momentum
at discrete times, is SYNOPSIS105, item 35; the kinetic diffusion
refreshes it continuously.

* **30. Invariance, contraction, and hypocoercivity.** The probability
  $\boldsymbol\pi(dx\,dp)\propto e^{-V(x)-\|p\|^2/2}\,dx\,dp=\pi\otimes N(0,I)$
  is invariant, and its $x$-marginal is $\pi$. The process is not
  reversible: the law solves
  $$\partial_t\boldsymbol\pi_t=\nabla\cdot\left(\boldsymbol\pi_t\,J_\gamma
  \nabla\log\frac{\boldsymbol\pi_t}{\boldsymbol\pi}\right),\qquad
  J_\gamma(a,b)=(-b,\;a+\gamma b),$$
  where $J_\gamma$ acts on the pair of $x$- and $p$-gradients. This is
  a damped Hamiltonian flow of the relative entropy rather than its $W_2$
  gradient flow. Since the noise acts on $p$ only, Poincaré and logarithmic
  Sobolev inequalities do not give decay directly. If
  $0\prec\alpha I\preceq\nabla^2V\preceq\beta I$ and
  $\gamma\ge\sqrt{2\beta}$, two copies driven by the same Brownian motion
  contract at rate $\alpha/\gamma$ in the norm
  $\|x\|^2+\|x+2p/\gamma\|^2$. If $\pi$ satisfies a Poincaré inequality
  with constant $1/\alpha$, $V$ is $\beta$-smooth, and
  $\gamma=c_0\sqrt\beta$, then the relative density $f_t=d\boldsymbol\pi_t/d\boldsymbol\pi-1$
  satisfies
  $$\|f_t\|^2+\tfrac1\beta\|\nabla_xf_t\|^2+\|\nabla_pf_t\|^2
  \le Ce^{-c\alpha t/\sqrt\beta}\bigl(\|f_0\|^2+\tfrac1\beta\|\nabla_xf_0\|^2
  +\|\nabla_pf_0\|^2\bigr)$$
  in $L^2(\boldsymbol\pi)$, with $c$ depending only on $c_0$ and $C$
  universal. A logarithmic Sobolev inequality gives the same rate for
  relative entropy plus a twisted Fisher information. This is the
  hypocoercive mechanism of CKMA SYNOPSIS34, item 75, in a confining
  potential.

### The ordinary differential equation method

For the recursion of item 4, the **limiting equation** is
$\dot\theta=-h(\theta)$, with flow $\Phi_t$. A compact set $A$ is
**invariant** if $\Phi_t(A)=A$ for all real $t$. It is **internally chain
transitive** if, in addition, for all $x,y\in A$ and all
$\varepsilon,T>0$ there are points $x_0,\ldots,x_n=y$ in $A$ with
$\|x_0-x\|<\varepsilon$ such that the trajectory from each $x_i$ enters
the $\varepsilon$-neighbourhood of $x_{i+1}$ after a time at least $T$.

* **31. Benaïm's limit-set theorem.** Suppose $h$ is globally Lipschitz,
  $a_n>0$, $\sum a_n=\infty$, $\sum a_n^2<\infty$, $(M_n)$ is a
  martingale difference sequence with respect to
  $\mathcal F_n=\sigma(\theta_0,M_1,\ldots,M_n)$ satisfying
  $\mathbb E[\|M_{n+1}\|^2\mid\mathcal F_n]\le K(1+\|\theta_n\|^2)$, and
  $\sup_n\|\theta_n\|<\infty$ almost surely. Then almost surely $\theta_n$
  converges to a, possibly sample-path-dependent, compact connected
  internally chain transitive invariant set of the limiting equation.
  Consequently, if $U\ge0$ is continuously differentiable,
  $U(\theta)\to\infty$ as $\|\theta\|\to\infty$, the set
  $H=\{U=0\}$ is nonempty, and $\langle h,\nabla U\rangle\ge0$ with
  equality exactly on $H$, then $\theta_n$ converges to a subset of $H$.
  If the only internally chain transitive invariant sets are isolated
  equilibria, $\theta_n$ converges to an equilibrium. The interpolated
  iterates track trajectories of the limiting equation on every finite
  time window, which is the ordinary differential equation method of
  Kushner–Clark and Ljung.

* **32. Stability by the scaling limit.** Suppose the hypotheses of item
  31 other than boundedness hold. Suppose further that
  $h_c(\theta)=h(c\theta)/c$ converges, as $c\to\infty$, uniformly on
  compact sets to a limit $h_\infty$, and that the origin is the unique
  globally asymptotically stable equilibrium of
  $\dot\theta=-h_\infty(\theta)$. Then $\sup_n\|\theta_n\|<\infty$ almost
  surely, so the conclusion of item 31 holds (Borkar–Meyn). For example,
  if $h(\theta)=A\theta+b+o(\|\theta\|)$ with $-A$ Hurwitz, then
  $h_\infty(\theta)=A\theta$. Boundedness of the iterates is otherwise not
  automatic.

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

### Fluctuations, stability, and resampling of particle filters

In the indexing of Del Moral, let $(X_n)_{n\ge0}$ be a Markov chain with
initial law $\eta_0$ and kernels $M_n$, and let $G_n>0$ be bounded
potentials. Put
$$\gamma_n(f)=\mathbb E\Bigl[f(X_n)\prod_{p=0}^{n-1}G_p(X_p)\Bigr],\qquad
\eta_n=\gamma_n/\gamma_n(1),$$
$$Q_{p,n}f(x)=\mathbb E\Bigl[f(X_n)\prod_{q=p}^{n-1}G_q(X_q)\Bigm|X_p=x\Bigr].$$
With $G_p(x)=p(y_p\mid x)$, $\eta_n$ is the one-step predictor $\eta_n^-$
of item 19 and $\gamma_n(1)$ is the likelihood of $y_0,\ldots,y_{n-1}$. The
**bootstrap particle model** draws $\xi_0^1,\ldots,\xi_0^N$ independently
from $\eta_0$ and, given generation $n-1$, draws generation $n$
independently from $\sum_iG_{n-1}(\xi_{n-1}^i)M_n(\xi_{n-1}^i,\cdot)\big/
\sum_iG_{n-1}(\xi_{n-1}^i)$; that is, multinomial selection followed by
mutation. Write $\eta_n^N$ for the empirical measure of generation $n$ and
$\gamma_n^N(1)=\prod_{p<n}\eta_p^N(G_p)$, the estimator of item 20.

* **33. Central limit theorem for Feynman–Kac particle models.**
  Suppose $\inf_xG_p(x)>0$ for every $p$. For bounded measurable $f$ and
  fixed $n$, as $N\to\infty$,
  $$\sqrt N\bigl(\eta_n^N(f)-\eta_n(f)\bigr)\Rightarrow
  N\bigl(0,\sigma_n^2(f)\bigr),\qquad
  \sigma_n^2(f)=\sum_{p=0}^n
  \frac{\eta_p\bigl([Q_{p,n}(f-\eta_nf)]^2\bigr)}{\eta_p(Q_{p,n}1)^2},$$
  and
  $$\sqrt N\left(\frac{\gamma_n^N(1)}{\gamma_n(1)}-1\right)\Rightarrow
  N\left(0,\sum_{p=0}^{n}\left[\frac{\eta_p\bigl((Q_{p,n}1)^2\bigr)}
  {\eta_p(Q_{p,n}1)^2}-1\right]\right).$$
  Each summand is the variance contributed by the sampling at
  generation $p$, propagated to time $n$ by the normalized semigroup.
  Without further assumptions these asymptotic variances may grow
  exponentially in $n$.

* **34. Uniform-in-time particle approximation.** Suppose there are
  $\varepsilon_G,\varepsilon_M\in(0,1]$ such that, for all $n$ and all
  $x,x'$,
  $$G_n(x)\ge\varepsilon_GG_n(x'),\qquad
  M_n(x,\cdot)\ge\varepsilon_MM_n(x',\cdot).$$
  Then for every $p\ge1$ there is $c_p<\infty$ such that
  $$\sup_{n\ge0}\ \sup_{\mathop{\mathrm{osc}}(f)\le1}
  \sqrt N\,\Bigl(\mathbb E\bigl|\eta_n^N(f)-\eta_n(f)\bigr|^p\Bigr)^{1/p}
  \le\frac{c_p}{\varepsilon_M^2\varepsilon_G},$$
  where $\mathop{\mathrm{osc}}(f)=\sup f-\inf f$. The mixing hypothesis
  makes the normalized Feynman–Kac semigroup forget its initial condition
  geometrically, and this forgetting stops the local sampling errors from
  accumulating. The second hypothesis holds, for instance, for a kernel
  with density bounded above and below on a compact state space; it fails
  for most noncompact state spaces, where time-uniform results require
  localized or Lyapunov-type versions.

A resampling step maps weighted particles $(x_i,w_i)$, with
$\sum_iw_i=1$, to $N$ equally weighted particles in which $x_i$ appears
$m_i$ times. It is **unbiased** if $\mathbb E[m_i\mid x,w]=Nw_i$.
**Multinomial resampling** draws $(m_i)$ from the multinomial law with
$N$ trials and probabilities $w_i$. **Residual resampling** keeps
$\lfloor Nw_i\rfloor$ copies of $x_i$ and allocates the remaining
$R=N-\sum_i\lfloor Nw_i\rfloor$ copies multinomially with probabilities
proportional to $Nw_i-\lfloor Nw_i\rfloor$. **Systematic resampling** uses
the single uniform $U$ and
$m_i=\lfloor N(w_1+\cdots+w_i)+U\rfloor-\lfloor N(w_1+\cdots+w_{i-1})+U\rfloor$.

* **35. Unbiased resampling and variance.** Multinomial, residual, and
  systematic resampling are unbiased, so the resampled average
  $N^{-1}\sum_im_if(x_i)$ has conditional mean $\sum_iw_if(x_i)$. Its
  conditional variance under multinomial resampling is
  $N^{-1}\mathop{\mathrm{Var}}_w(f)$, where
  $\mathop{\mathrm{Var}}_w(f)=\sum_iw_if(x_i)^2-(\sum_iw_if(x_i))^2$.
  Under residual resampling it is
  $RN^{-2}\mathop{\mathrm{Var}}_{\bar w}(f)$, where $\bar w$ are the
  normalized residual weights. Since $w$ is the mixture of the retained
  weights and $\bar w$ with weight $R/N$ on $\bar w$, this is never larger
  than the multinomial variance, for every $f$. Systematic resampling uses
  less randomness but has no general variance ordering with respect to
  multinomial resampling. Any unbiased scheme preserves the unbiasedness
  of item 20.

### Variational data assimilation

Consider the **stochastic dynamics model**
$v_{j+1}=\Psi(v_j)+\xi_j$, $v_0\sim N(m_0,C_0)$, with observations
$y_{j+1}=h(v_{j+1})+\eta_{j+1}$, $j=0,\ldots,J-1$, where
$\xi_j\sim N(0,\Sigma)$, $\eta_{j+1}\sim N(0,\Gamma)$, $C_0,\Sigma,\Gamma>0$,
and all of these are independent. Write $|a|_C^2=a^\top C^{-1}a$ and, for a
path $v=(v_0,\ldots,v_J)$,
$$I(v;y)=\tfrac12|v_0-m_0|_{C_0}^2+\sum_{j=0}^{J-1}
\Bigl(\tfrac12|v_{j+1}-\Psi(v_j)|_\Sigma^2
+\tfrac12|y_{j+1}-h(v_{j+1})|_\Gamma^2\Bigr).$$
**Weak-constraint 4DVAR** minimizes $I(\cdot;y)$. **Strong-constraint
4DVAR** imposes the deterministic dynamics $v_{j+1}=\Psi(v_j)$ and minimizes
$I_{\det}(v_0;y)=\tfrac12|v_0-m_0|_{C_0}^2
+\sum_j\tfrac12|y_{j+1}-h(\Psi^{(j+1)}(v_0))|_\Gamma^2$
over the initial state only. **3DVAR** is the filter that, at each step,
minimizes the analogous one-step objective with a fixed model covariance.

* **36. 4DVAR as maximum a posteriori estimation.** The smoothing
  posterior of $v$ given $y$ has Lebesgue density proportional to
  $\exp(-I(v;y))$, and in the deterministic model the posterior of $v_0$
  has density proportional to $\exp(-I_{\det}(v_0;y))$. If $\Psi$ and $h$
  are continuously differentiable, each infimum is attained, and for all
  $u_1,u_2$
  $$\lim_{\delta\to0}\frac{\mathbb P(B(u_1,\delta)\mid y)}
  {\mathbb P(B(u_2,\delta)\mid y)}=\exp\bigl(I(u_2;y)-I(u_1;y)\bigr),$$
  with the analogous statement for $I_{\det}$. Thus the 4DVAR minimizers
  are exactly the posterior modes in the small-ball sense. For linear
  $\Psi$ and $h$ the posterior is Gaussian and the minimizer is the
  Kalman smoother mean; in nonlinear models the mode and mean differ in
  general, and the minimizer carries no uncertainty quantification. The
  objective of strong-constraint 4DVAR is often harder to minimize for
  chaotic dynamics, despite its lower dimension.

### Entropy-regularized mean-field training

In the setting of item 7, take a convex differentiable loss in its
second argument, a regularization parameter $\lambda>0$, and an inverse
temperature $\beta\in(0,\infty)$. Noisy gradient descent with weight decay,
$d\theta_i=-\bigl(N\nabla_{\theta_i}\mathcal R(\rho_N)+\lambda\theta_i\bigr)dt
+\sqrt{2/\beta}\,dW_i$, has the **mean-field Langevin** limit
$$\partial_t\rho=\nabla_\theta\cdot\left(\rho\nabla_\theta\Bigl(
\frac{\delta\mathcal R}{\delta\rho}+\frac\lambda2\|\theta\|^2\Bigr)\right)
+\beta^{-1}\Delta_\theta\rho,$$
the $W_2$ gradient flow of the free energy
$\mathcal F_\beta(\rho)=\mathcal R(\rho)+\frac\lambda2\int\|\theta\|^2d\rho
+\beta^{-1}\int\rho\log\rho$.

* **37. Free energy and the Gibbs fixed point.** Because
  $\rho\mapsto f_\rho$ is linear and the loss is convex, $\mathcal R$ is
  convex along linear interpolations $(1-s)\rho_0+s\rho_1$, and the entropy
  makes $\mathcal F_\beta$ strictly convex in that sense. Hence
  $\mathcal F_\beta$ has at most one minimizer. Under bounded smooth
  interaction derivatives, a minimizer $\rho^*$ exists and is
  characterized by the self-consistent Gibbs equation
  $$\rho^*(\theta)\propto\exp\Bigl(-\beta\Bigl[
  \frac{\delta\mathcal R}{\delta\rho}(\rho^*)(\theta)
  +\frac\lambda2\|\theta\|^2\Bigr]\Bigr).$$
  Along the mean-field Langevin flow, $\mathcal F_\beta(\rho_t)$ is
  nonincreasing, with dissipation $\beta^{-2}$ times the relative Fisher
  information of $\rho_t$ with respect to the Gibbs measure obtained by
  inserting $\rho_t$ for $\rho^*$ on the right-hand side.
  Under such regularity hypotheses the flow converges to $\rho^*$
  (Mei–Montanari–Nguyen; Hu, Ren, Šiška, and Szpruch); exponential rates
  follow from a uniform logarithmic Sobolev inequality for those Gibbs
  measures. The convexity is in the linear structure of measures, not
  displacement convexity, and it is what replaces the nonconvex landscape
  in parameter space. As $\beta\to\infty$ one recovers the noiseless flow of
  item 7, for which global convergence needs separate hypotheses
  (Chizat–Bach).

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

### Training objectives and discrete-time samplers

For the forward diffusion of item 10, let $p_{t|0}(x\mid x_0)$ be its
transition density from time $0$. For an affine drift and scalar $g$, as
in the usual noising processes,
$X_t\mid X_0\sim N(A_tX_0,\sigma_t^2I)$ for deterministic $A_t$ and
$\sigma_t>0$, and $\nabla_x\log p_{t|0}(X_t\mid X_0)=-Z/\sigma_t$ where
$X_t=A_tX_0+\sigma_tZ$.

* **38. Denoising score matching along a diffusion.** Fix $t>0$, suppose
  $p_t$ is smooth and positive, and suppose
  $\mathbb E\|\nabla_x\log p_{t|0}(X_t\mid X_0)\|^2<\infty$. Then for every
  measurable $s$ with $\mathbb E\|s(X_t)\|^2<\infty$,
  $$\mathbb E\|s(X_t)-\nabla\log p_t(X_t)\|^2
  =\mathbb E\|s(X_t)-\nabla_x\log p_{t|0}(X_t\mid X_0)\|^2-C_t,$$
  where $C_t=\mathbb E\|\nabla_x\log p_{t|0}(X_t\mid X_0)
  -\nabla\log p_t(X_t)\|^2$ does not depend on $s$. The identity is the
  Pythagorean relation for the conditional expectation
  $\nabla\log p_t(X_t)=\mathbb E[\nabla_x\log p_{t|0}(X_t\mid X_0)\mid X_t]$,
  which extends item 11 to every noising kernel. Integrating against a
  weight $w(t)\ge0$ gives a regression objective whose excess risk is the
  time-integrated score error of item 15 when $w=g^2$ for scalar $g$.
  In the Gaussian case $C_t\le d/\sigma_t^2$, which is not integrable near
  $t=0$ when $\sigma_t^2$ is of order $t$; hence the time integral is
  truncated at a positive time, or weighted by $w(t)=\sigma_t^2$, which
  turns the objective into the noise-prediction loss
  $\mathbb E\|\sigma_ts(X_t)+Z\|^2$.

* **39. Gaussian reverse conditionals and the diffusion evidence bound.**
  In the chain of item 22, with $\bar\alpha_0=1$ and $t\ge2$,
  $$Z_{t-1}\mid(Z_t,Z_0=x)\sim N\bigl(m_t(x,Z_t),s_t^2I\bigr),\quad
  m_t=\frac{\sqrt{1-\beta_t}\,(1-\bar\alpha_{t-1})Z_t
  +\sqrt{\bar\alpha_{t-1}}\,\beta_tx}{1-\bar\alpha_t},\quad
  s_t^2=\frac{\beta_t(1-\bar\alpha_{t-1})}{1-\bar\alpha_t}.$$
  For a reverse model $p_\theta(z_T)\prod_tp_\theta(z_{t-1}\mid z_t)$,
  $$-\log p_\theta(x)\le
  \mathbb E[-\log p_\theta(x\mid Z_1)]
  +\sum_{t=2}^T\mathbb E\,\mathop{\mathrm{KL}}\bigl(q(\cdot\mid Z_t,x)\,\|\,
  p_\theta(\cdot\mid Z_t)\bigr)
  +\mathop{\mathrm{KL}}\bigl(q(Z_T\mid x)\,\|\,p_\theta(Z_T)\bigr),$$
  where $q$ is the forward chain started at $x$; this is the evidence
  lower bound of SYNOPSIS105, item 15, for the latent path. If
  $p_\theta(\cdot\mid z_t)=N(\mu_\theta(z_t,t),s_t^2I)$ and
  $\mu_\theta=(1-\beta_t)^{-1/2}\bigl(z_t-\beta_t(1-\bar\alpha_t)^{-1/2}
  \varepsilon_\theta(z_t,t)\bigr)$, then the $t$-th term equals
  $$\frac{\beta_t^2}{2s_t^2(1-\beta_t)(1-\bar\alpha_t)}\,
  \mathbb E\|\varepsilon-\varepsilon_\theta(Z_t,t)\|^2,
  \qquad Z_t=\sqrt{\bar\alpha_t}\,x+\sqrt{1-\bar\alpha_t}\,\varepsilon.$$
  Dropping these weights gives the usual noise-prediction objective,
  a weighted sum of the denoising score matching losses of item 38 at
  discrete noise levels.

Consider the variance-exploding forward process $dX_t=dW_t$, $X_0\sim\pi$,
so $\pi_t=\pi*N(0,tI)$. Let $0=\tau_0<\cdots<\tau_N<T$ with steps
$h_n=\tau_{n+1}-\tau_n$, put $\delta=T-\tau_N$, and let $\hat s_t$ be a
score estimate. The **DDPM sampler** starts from $\hat X_0\sim N(0,TI)$ and
sets
$$\hat X_{\tau_{n+1}}=\hat X_{\tau_n}+h_n\hat s_{T-\tau_n}(\hat X_{\tau_n})
+\sqrt{\frac{(T-\tau_{n+1})h_n}{T-\tau_n}}\,\xi_{n+1},$$
with independent standard normal $\xi_n$, which freezes the denoiser of
item 21 on each step.

* **40. Convergence of diffusion sampling under a second-moment
  assumption.** Suppose only that $m_2^2=\mathbb E_\pi\|X\|^2<\infty$, and
  that $h_n\le\bar h(T-\tau_n)$ with $\bar h\le1/2$. Put
  $\varepsilon_{\mathrm{sc}}^2=\sum_nh_n\mathbb E_{\pi_{T-\tau_n}}
  \|\hat s_{T-\tau_n}-\nabla\log\pi_{T-\tau_n}\|^2$. Then the law
  $\hat\pi$ of $\hat X_{\tau_N}$ satisfies
  $$\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\le\frac{m_2^2}{2T}
  +4\varepsilon_{\mathrm{sc}}^2+2\bar h\,d\bigl(1+\log(T/\delta)\bigr),$$
  the three terms being initialization, score, and discretization error.
  With $T$ of order $m_2^2/\varepsilon^2$, $\bar h$ of order
  $\varepsilon^2/(d\log(T/\delta))$, and steps proportional to the
  remaining time, $N=O\bigl(d\varepsilon^{-2}
  \log^2(m_2^2/(\delta\varepsilon^2))\bigr)$ steps give
  $\mathop{\mathrm{KL}}(\pi_\delta\|\hat\pi)\lesssim\varepsilon^2
  +\varepsilon_{\mathrm{sc}}^2$. No log-concavity, functional inequality,
  or density of $\pi$ is required, and $W_2(\pi,\pi_\delta)\le\sqrt{\delta d}$.
  The earlier polynomial bounds of Chen, Chewi, Li, Li, Salim, and Zhang
  assumed Lipschitz scores along the forward process. The step count is
  linear in $d$ up to logarithmic factors, but the score error
  $\varepsilon_{\mathrm{sc}}$ must itself be small, as in item 15.

### Marginal-preserving dynamics and bridge iterations

* **41. A family of diffusions with prescribed marginals.** Let $\mu_t$,
  $t\in[0,1]$, be smooth positive densities solving
  $\partial_t\mu_t+\nabla\cdot(\mu_tv_t)=0$, and let $\epsilon_t\ge0$ be
  continuous. Then $\mu_t$ also solves the Fokker–Planck equation of
  $$dX_t=\bigl(v_t+\epsilon_t\nabla\log\mu_t\bigr)(X_t)\,dt
  +\sqrt{2\epsilon_t}\,dW_t,$$
  because $\epsilon_t\nabla\cdot(\mu_t\nabla\log\mu_t)=\epsilon_t\Delta\mu_t$.
  If that Fokker–Planck equation has unique solutions in the class
  considered, $X_0\sim\mu_0$ gives $X_t\sim\mu_t$ for all $t$; the same
  holds in reverse time with drift $v_t-\epsilon_t\nabla\log\mu_t$. For a
  forward diffusion with scalar $g$, the choices $\epsilon=0$ and
  $\epsilon=g^2/2$ with $v_t=f-\tfrac12g^2\nabla\log p_t$ recover the
  probability-flow equation and the original diffusion of item 10. For a
  **stochastic interpolant** $X_t=I_t(X_0,X_1)+\gamma_tZ$, with
  $I_0(x_0,x_1)=x_0$, $I_1(x_0,x_1)=x_1$, $\gamma_0=\gamma_1=0$,
  $\gamma_t>0$ on $(0,1)$, and $Z$ standard normal independent of the
  coupling,
  $$v_t(x)=\mathbb E[\partial_tI_t(X_0,X_1)+\dot\gamma_tZ\mid X_t=x],\qquad
  \nabla\log\mu_t(x)=-\gamma_t^{-1}\mathbb E[Z\mid X_t=x],$$
  so velocity and score are both population least-squares regressions, as
  in item 14. Flow matching is the case $\gamma=0$ of the velocity
  regression; score-based diffusion is a case of the score regression.

For path measures $Q,R$ on $C([0,T];\mathbb R^d)$, write $Q_0,Q_T$ for the
endpoint laws and $Q^x$ for a regular conditional law of $Q$ given
$X_0=x$. The **half-bridge** problems minimize $\mathop{\mathrm{KL}}(Q\|P)$
over $Q$ with one prescribed endpoint law. **Iterative proportional
fitting** sets $P^0=R$ and alternately takes $P^{2k+1}$ to be the
half-bridge from $P^{2k}$ with terminal law $\mu_T$ and $P^{2k+2}$ the
half-bridge from $P^{2k+1}$ with initial law $\mu_0$.

* **42. Half-bridges and iterative proportional fitting.** The chain
  rule
  $\mathop{\mathrm{KL}}(Q\|P)=\mathop{\mathrm{KL}}(Q_0\|P_0)
  +\int\mathop{\mathrm{KL}}(Q^x\|P^x)\,Q_0(dx)$
  shows that if $\mathop{\mathrm{KL}}(\mu_0\|P_0)<\infty$, the unique
  half-bridge with initial law $\mu_0$ is
  $\int P^x\,\mu_0(dx)=\frac{d\mu_0}{dP_0}(X_0)\cdot P$, with value
  $\mathop{\mathrm{KL}}(\mu_0\|P_0)$; similarly at the terminal time, where
  it is simulated by running the time reversal of $P$ from $\mu_T$. Every
  iterate therefore has the form $f_k(X_0)g_k(X_T)\cdot R$, keeps the
  reference bridges of item 13, and has endpoint couplings equal to the
  Sinkhorn iterates for the kernel $R_{0T}$, CKMA SYNOPSIS39, item 90.
  If $P^*$ is the Schrödinger bridge of item 13 with
  $\mathop{\mathrm{KL}}(P^*\|R)<\infty$, then each half-step is an entropy
  projection onto a linear family containing $P^*$, so
  $$\mathop{\mathrm{KL}}(P^*\|P^k)=\mathop{\mathrm{KL}}(P^*\|P^{k+1})
  +\mathop{\mathrm{KL}}(P^{k+1}\|P^k),$$
  as in item 23. Hence $\mathop{\mathrm{KL}}(P^*\|P^k)$ is nonincreasing
  and $\sum_k\mathop{\mathrm{KL}}(P^{k+1}\|P^k)\le\mathop{\mathrm{KL}}(P^*\|R)$.
  The static iteration converges to the Schrödinger coupling under these
  hypotheses (Rüschendorf). The diffusion Schrödinger bridge of De Bortoli,
  Thornton, Heng, and Doucet implements the half-steps by learned
  time reversals as in items 10 and 38.

## Reference guide

### Correspondence with the subdivisions

- **[112A](#synopsis-112a)**: Jordan, Kinderlehrer, and Otto, and Figalli and
  Glaudo, carry the minimizing-movement scheme. Pavliotis carries the Langevin diffusion.
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
is treated in the consulted Bishop–Bishop text. Del Moral's 2013 volume
is in `References`; his 2004 Feynman–Kac monograph is in `ReferencesSuppl`
and was used for the third expansion.

### Third expansion (items 25–42)

For 112A, Chewi's manuscript was read in Theorems 1.2.21–1.2.26 (Poincaré
and $\chi^2$ decay, logarithmic Sobolev and KL decay; item 26), Theorems
4.1.2 and 4.2.7 (coupling bias and the Vempala–Wibisono bound; item 27),
Section 10.1 and display (10.1.1) (stochastic-gradient Langevin; item 28),
Theorems 7.3.4, 7.3.5, and 7.6.5 with the bibliographical notes to Chapter 7
(MALA; item 29), and Section 5.3, Theorems 5.3.6, 5.3.14, and 5.3.15
(kinetic Langevin; item 30). Robert and Casella, Section 7.8, was read for
the acceptance rates $0.234$ and $0.574$; the papers of Roberts, Gelman, and
Gilks and of Roberts and Rosenthal were not available locally, and item 29
states their product-target hypotheses only in outline. Figalli–Glaudo,
Section 3.3, was read for the JKO scheme on bounded convex domains; the
whole-space hypotheses of item 25 are those of the original JKO paper, which
is not local. Borkar's second edition, Chapter 2 (assumptions (A1)–(A4),
Theorem 2.1, Corollaries 2.1–2.2) and Chapter 4 (assumption (A9), Theorem 4.1),
was read for items 31–32, with the signs converted to the convention of item 4.

For 112B, Del Moral's 2004 monograph (local in `ReferencesSuppl`) was read in
Chapter 9, Theorem 9.3.1, Corollary 9.3.1, and Propositions 9.4.1–9.4.2, for
the fluctuation variances in item 33, which are specialized here to
multinomial selection, and in Theorem 7.4.4 with conditions (G) and $(M)_m$
of Section 4.4, for item 34 with $m=1$. Liu, Section 3.4, and Robert–Casella,
Section 14.3.5, were read for residual and systematic resampling; the
variance comparison in item 35 is the law of total variance. Law, Stuart, and
Zygalakis, Theorems 2.8, 2.11, 3.10, and 3.12 and Section 4.2.1, were read for
item 36. Item 37 has no local full-text source; it follows Mei, Montanari, and
Nguyen and the convergence theory of Hu, Ren, Šiška, and Szpruch from the
primary literature, and is stated with its regularity hypotheses only in
outline.

For 112C, Chewi, Chapter 12 (Sections 12.1–12.3, Theorem 12.3.2 and Lemma
12.3.3), was read for items 38, 40, and 41, including the denoising
identity, the probability-flow variants, and the stochastic-interpolant
regression. Bishop–Bishop, Sections 20.1.2 and 20.2.2–20.2.4, was read for
item 39. Item 42 uses the chain rule for relative entropy and the projection
identity of item 23; the convergence of iterative proportional fitting is
due to Rüschendorf, not consulted locally, and the finite-state rate is
CKMA SYNOPSIS39, item 90.

Local texts directly consulted or identified for this selection:

- [Law, Stuart, and Zygalakis, *Data Assimilation: A Mathematical Introduction*](../lean-CKMA/ReferencesSuppl/LawStuartZygalakis2015DataAssimilationMathematicalIntroduction-Springer.TAM62.pdf).
  The two ensemble Kalman variants in Sections 4.2.3–4.2.4 were read.
- [Bishop and Bishop, *Deep Learning: Foundations and Concepts*](../lean-CKMA/References/BishopBishop2024DeepLearningFoundationsConcepts-Springer.pdf).
  Chapter 20 was consulted for diffusion and score models.
- [Chewi, *Log-Concave Sampling*](../lean-CKMA/References/Chewi2026LogConcaveSampling-AuthorManuscript.pdf).
  Theorem 4.3.6 was read; for items 25–42 also the passages listed above.
- [Pavliotis, *Stochastic Processes and Applications*](../lean-CKMA/References/Pavliotis2014StochasticProcessesApplications-SpringerTAM.pdf).
- [Kushner and Yin, *Stochastic Approximation and Recursive Algorithms and Applications*](../lean-CKMA/References/KushnerYin2003StochasticApproximationRecursiveAlgorithmsApplications2ndEd-Springer.SMAP35.pdf).
- [Borkar, *Stochastic Approximation: A Dynamical Systems Viewpoint*](../lean-CKMA/References/Borkar2023StochasticApproximationDynamicalSystemsViewpoint2ndEd-SpringerHindustanTRIM48.pdf).
- [Ambrosio, Gigli, and Savaré, *Gradient Flows*](../lean-CKMA/References/AmbrosioGigliSavaré2008GradientFlowsMetricSpacesSpaceProbabilityMeasures2ndEd-Birkhäuser.LMETH.pdf).
- [Del Moral, *Mean Field Simulation for Monte Carlo Integration*](../lean-CKMA/References/DelMoral2013MeanFieldSimulationMonteCarloIntegration-ChapmanHallCRC.MSAP126.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. I](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications1FBSDEsControl-SpringerPTSM83.pdf).
- [Carmona and Delarue, *Probabilistic Theory of Mean Field Games*, Vol. II](../lean-CKMA/References/CarmonaDelarue2018ProbabilisticTheoryMeanFieldGamesApplications2CommonNoiseMasterEquations-SpringerPTSM84.pdf).
- [Figalli and Glaudo, *An Invitation to Optimal Transport, Wasserstein Distances, and Gradient Flows*](../lean-CKMA/References/FigalliGlaudo2021InvitationOptimalTransportWassersteinDistancesGradientFlows-EMS.TextbooksMath.pdf).
  Section 3.3 (JKO scheme) was read.
- [Del Moral, *Feynman–Kac Formulae: Genealogical and Interacting Particle Systems with Applications*](../lean-CKMA/ReferencesSuppl/Moral2004FeynmanKacFormulaeGenealogicalInteractingParticleSystemsApplications-Springer.PIA.pdf).
  Sections 4.4, 7.4, and 9.3–9.4 were read.
- [Robert and Casella, *Monte Carlo Statistical Methods*](../lean-CKMA/ReferencesSuppl/RobertCasella2004MonteCarloStatisticalMethods2ndEd-Springer.pdf).
  Sections 7.8 and 14.3.5 were read.
- [Liu, *Monte Carlo Strategies in Scientific Computing*](../lean-CKMA/ReferencesSuppl/Liu2004MonteCarloStrategiesScientificComputing-SpringerSerStat.pdf).
  Section 3.4 (residual resampling) was read.
- [Peyré and Cuturi, *Computational Optimal Transport*](../lean-CKMA/References/PeyréCuturi2019ComputationalOptimalTransportApplicationsDataSciences-NowPublishers.FnTML11.pdf).
