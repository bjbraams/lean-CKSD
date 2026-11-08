module

public import CKSD.Processes.TimeSeries.CentralLimit
public import CKSD.Processes.TimeSeries.Wold
public import CKSD.Processes.TimeSeries.LongRunVariance
public import CKSD.Processes.TimeSeries.StationaryGaussian
public import CKSD.Processes.TimeSeries.Garch

/-!
# Stationary time series

Entry module for the time-series part of Section 106:

* `CKSD.Processes.TimeSeries.CentralLimit`: the martingale central limit theorem for triangular
  arrays and the independent case of Bartlett's theorem (GAPS 106.1 and 106.4);
* `CKSD.Processes.TimeSeries.Wold`: the Hilbert-space Wold decomposition (GAPS 106.2);
* `CKSD.Processes.TimeSeries.LongRunVariance`: long-run variance of the sample mean under
  absolutely summable autocovariances (GAPS 106.12);
* `CKSD.Processes.TimeSeries.StationaryGaussian`: existence of a stationary Gaussian sequence
  with a given positive semidefinite autocovariance (GAPS 106.14);
* `CKSD.Processes.TimeSeries.Garch`: stationary GARCH(1,1) series and moments (GAPS 106.18).

Time indices are integers for stationary constructions and natural numbers for observation
prefixes.
-/
