module

public import CKSD.Processes.TimeSeries.Wold
public import CKSD.Processes.TimeSeries.LongRunVariance
public import CKSD.Processes.TimeSeries.StationaryGaussian
public import CKSD.Processes.TimeSeries.Garch

/-!
# Stationary time series

The Hilbert-space Wold decomposition, summable-covariance long-run variance, stationary
Gaussian realization and stationary GARCH moment theory. Time indices are integers for
stationary constructions and natural numbers for observation prefixes.
Sources: GAPS 106.10, 106.12, 106.14 and 106.18.
-/
