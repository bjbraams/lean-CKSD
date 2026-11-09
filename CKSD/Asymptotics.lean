module

public import CKSD.Asymptotics.MEstimators
public import CKSD.Asymptotics.Statistics
public import CKSD.Asymptotics.Framework
public import CKSD.Asymptotics.Estimators
public import CKSD.Asymptotics.Experiments
public import CKSD.Asymptotics.AsymptoticTheory
public import CKSD.Asymptotics.HigherOrder
public import CKSD.Asymptotics.LikelihoodTests
public import CKSD.Asymptotics.RatesOfConvergence
public import CKSD.Asymptotics.Semiparametric
public import CKSD.Asymptotics.Expansions
public import CKSD.Asymptotics.Bootstrap

/-!
# Section 102: Asymptotic statistics

Entry module for the CKSD formalization of Section 102.

* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.Framework`, `CKSD.Asymptotics.Statistics`:
  empirical statistics, contiguity, stochastic orders, local experiments, and statistical
  functionals.
* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.MultivariateCLT`: weak convergence, stochastic
  algebra, laws of large numbers, and central limit theorems.
* `CKSD.Asymptotics.Estimators` and its parts (`MaximumLikelihood`, `ZEstimators`, `Quantiles`,
  `UStatistics`, `LikelihoodSupport`), `CKSD.Asymptotics.MEstimators`,
  `CKSD.Asymptotics.RatesOfConvergence`, `CKSD.Asymptotics.AsymptoticTheory`: consistency, rates,
  and asymptotic normality of estimators.
* `CKSD.Asymptotics.Experiments`, `CKSD.Asymptotics.LikelihoodTests`: contiguity, Le Cam's lemmas,
  local asymptotic normality, and the likelihood-ratio, Wald, and score tests.
* `CKSD.Asymptotics.Semiparametric`: semiparametric efficiency, cross-fitting, and adaptation.
* `CKSD.Asymptotics.HigherOrder`, `CKSD.Asymptotics.Expansions`, `CKSD.Asymptotics.Bootstrap`:
  robustness, Edgeworth and saddlepoint expansions, and the bootstrap.
-/
