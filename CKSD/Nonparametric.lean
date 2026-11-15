module -- shake: keep-all

public import CKSD.Nonparametric.Estimation
public import CKSD.Nonparametric.Density
public import CKSD.Nonparametric.SmoothingRates
public import CKSD.Nonparametric.HolderRegressionMinimax
public import CKSD.Nonparametric.Models
public import CKSD.Nonparametric.GoodnessOfFit
public import CKSD.Nonparametric.IsotonicRegression
public import CKSD.Nonparametric.ModelSelection
public import CKSD.Nonparametric.GaussianProjection
public import CKSD.Nonparametric.EmpiricalCovariance
public import CKSD.Nonparametric.TracyWidom
public import CKSD.Nonparametric.HighDimensional
public import CKSD.Nonparametric.LowerBounds
public import CKSD.Nonparametric.SparseRecovery.Robust

/-!
# Section 103: Nonparametric and high-dimensional statistics

Entry module for the CKSD formalization of Section 103 of the synopsis: empirical distribution
functions, kernel density estimation and rank statistics (`CKSD.Nonparametric.Estimation`),
density estimation (`CKSD.Nonparametric.Density`), regression smoothing and Hölder rates
(`CKSD.Nonparametric.SmoothingRates`, `CKSD.Nonparametric.HolderRegressionMinimax`), the Gaussian
sequence and regression models (`CKSD.Nonparametric.Models`), distribution-free goodness-of-fit
tests (`CKSD.Nonparametric.GoodnessOfFit`), isotonic regression
(`CKSD.Nonparametric.IsotonicRegression`), penalized model selection
(`CKSD.Nonparametric.ModelSelection`, with the Gaussian projection tools of
`CKSD.Nonparametric.GaussianProjection`), empirical covariance and the Tracy–Widom law
(`CKSD.Nonparametric.EmpiricalCovariance`, `CKSD.Nonparametric.TracyWidom`), high-dimensional
estimation and testing (`CKSD.Nonparametric.HighDimensional`), minimax lower bounds
(`CKSD.Nonparametric.LowerBounds`), and sparse recovery
(`CKSD.Nonparametric.SparseRecovery.Robust`).
-/
