module

public import CKSD.Asymptotics.MEstimators
public import CKSD.Asymptotics.MEstimatorNormality
public import CKSD.Asymptotics.RegressionMEstimators
public import CKSD.Asymptotics.Statistics
public import CKSD.Asymptotics.Framework
public import CKSD.Asymptotics.Estimators
public import CKSD.Asymptotics.Experiments
public import CKSD.Asymptotics.AsymptoticTheory
public import CKSD.Asymptotics.HigherOrder
public import CKSD.Asymptotics.LikelihoodTests
public import CKSD.Asymptotics.RatesOfConvergence
public import CKSD.Asymptotics.Semiparametric
public import CKSD.Asymptotics.CrossFitting
public import CKSD.Asymptotics.Expansions
public import CKSD.Asymptotics.Bootstrap
public import CKSD.Asymptotics.Lindeberg.Basic
public import CKSD.Asymptotics.MartingaleCLT.Basic
public import CKSD.Asymptotics.ConvexArgmin.Basic
public import CKSD.Asymptotics.ConvexRegression.Basic
public import CKSD.Asymptotics.UStatisticsProjection
public import CKSD.Asymptotics.LipschitzChaining
public import CKSD.Asymptotics.LipschitzExpansion

/-!
# Section 102: Asymptotic statistics

Entry module for the CKSD formalization of Section 102.

* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.Framework`, `CKSD.Asymptotics.Statistics`:
  empirical statistics, contiguity, stochastic orders, local experiments, and statistical
  functionals.
* `CKSD.Asymptotics.Basic`, `CKSD.Asymptotics.MultivariateCLT`,
  `CKSD.Asymptotics.Lindeberg.Basic`, `CKSD.Asymptotics.MartingaleCLT.Basic`: weak convergence,
  stochastic algebra, laws of large numbers, and central limit theorems, including the
  Lindeberg–Feller theorem for triangular arrays and the martingale central limit theorem under
  bounded conditional variances.
* `CKSD.Asymptotics.Estimators` and its parts (`MaximumLikelihood`, `ZEstimators`, `Quantiles`,
  `UStatistics`, `UStatisticsProjection`, `LikelihoodSupport`), `CKSD.Asymptotics.MEstimators`,
  `CKSD.Asymptotics.MEstimatorNormality`, `CKSD.Asymptotics.RegressionMEstimators`
  with the chaining bounds of `CKSD.Asymptotics.LipschitzChaining` and
  `CKSD.Asymptotics.LipschitzExpansion`,
  `CKSD.Asymptotics.RatesOfConvergence`, `CKSD.Asymptotics.AsymptoticTheory`: consistency, rates,
  and asymptotic normality of estimators.
* `CKSD.Asymptotics.Experiments`, `CKSD.Asymptotics.LikelihoodTests`: contiguity, Le Cam's lemmas,
  local asymptotic normality, and the likelihood-ratio, Wald, and score tests.
* `CKSD.Asymptotics.Semiparametric`, `CKSD.Asymptotics.CrossFitting`: semiparametric efficiency,
  cross-fitting, and adaptation.
* `CKSD.Asymptotics.HigherOrder`, `CKSD.Asymptotics.Expansions`, `CKSD.Asymptotics.Bootstrap`:
  robustness, Edgeworth and saddlepoint expansions, and the bootstrap.
-/
