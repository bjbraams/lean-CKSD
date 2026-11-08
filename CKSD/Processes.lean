module

public import CKSD.Processes.Models
public import CKSD.Processes.TimeSeries
public import CKSD.Processes.Survival
public import CKSD.Processes.Sequential
public import CKSD.Processes.WaldIdentity
public import CKSD.Processes.ExtremeValueLimits
public import CKSD.Processes.BridgeLimits
public import CKSD.Processes.Extremes
public import CKSD.Processes.Spectral
public import CKSD.Processes.Kalman
public import CKSD.Processes.Dependence
public import CKSD.Processes.CountingProcesses

/-!
# Section 106: Stochastic processes and time series

Entry module for the CKSD formalization of Section 106.

* `CKSD.Processes.Basic`: weak stationarity, iid noise, sample autocovariances and the
  survival-analysis estimators;
* `CKSD.Processes.Independence`: independence of functions of disjoint blocks of an
  independent sequence and measurability of randomly indexed terms;
* `CKSD.Processes.Models`: Brownian bridge, hitting times and change-point statistics
  (GAPS 106.44);
* `CKSD.Processes.TimeSeries`: martingale central limit theorem, Bartlett's theorem, Wold
  decomposition, long-run variance, stationary Gaussian sequences and GARCH (GAPS 106.1, 106.2,
  106.4, 106.12, 106.14, 106.18);
* `CKSD.Processes.Spectral`: periodogram and lag-window estimators, the Kolmogorov–Szegő
  formula, Whittle estimation and spectral random fields (GAPS 106.6, 106.16, 106.17, 106.24);
* `CKSD.Processes.GaussianConditioning`, `CKSD.Processes.Kalman`: Gaussian conditioning and
  the Kalman filter (GAPS 106.7);
* `CKSD.Processes.Dependence`: mixing coefficients, the moving-block bootstrap and
  asymptotically efficient prediction under equivalent models (GAPS 106.11, 106.21);
* `CKSD.Processes.Survival`, `CKSD.Processes.CountingProcesses`: Nelson–Aalen and Kaplan–Meier
  asymptotics, Rebolledo's theorem and Cox regression (GAPS 106.28, 106.29, 106.30, 106.34);
* `CKSD.Processes.Sequential`, `CKSD.Processes.WaldIdentity`, `CKSD.Processes.BridgeLimits`:
  Wald's identity, Anscombe's theorem, Ville's inequality, Wald's fundamental identity and
  bridge limits of CUSUM statistics (GAPS 106.37, 106.38, 106.39, 106.41, 106.42);
* `CKSD.Processes.Extremes`, `CKSD.Processes.ExtremeValueLimits`: Poisson exceedance limits,
  regularly varying maxima, Pickands–Balkema–de Haan and the Hill estimator
  (GAPS 106.46–106.50).
-/
