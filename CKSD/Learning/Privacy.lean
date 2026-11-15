module -- shake: keep-all

public import CKSD.Learning.Privacy.Basic
public import CKSD.Learning.Privacy.Mechanisms
public import CKSD.Learning.Privacy.CentralLowerBounds
public import CKSD.Learning.Privacy.LocalEstimation

/-!
# Differential privacy and private estimation of a bounded mean

`CKSD.Learning.Privacy.Basic` contains basic composition of adaptive private releases and the
contraction of divergences under a locally private channel (GAPS 107.65, 107.75).

The remaining modules treat private estimation of a bounded mean. Data sets are vectors in
`ℝⁿ`, neighbouring when they differ in at most one coordinate. A central mechanism is a Markov
kernel from data sets to real releases. The clipped Laplace mechanism releases the mean of the
data clipped to `[-1,1]` plus Laplace noise of scale `2 / (n ε)`. Local mechanisms are
noninteractive: individual `i` releases `Zᵢ ∼ Qᵢ(· | Xᵢ)` through an `ε`-locally private kernel
to the real line, and an estimator is a measurable function of the releases. The target is the
mean of an unknown law on `[-1,1]` and the risk is the mean squared error.

* `CKSD.Learning.Privacy.Mechanisms`: central and local mechanisms and the central upper bound.
* `CKSD.Learning.Privacy.CentralLowerBounds`: two-point lower bounds for central estimation.
* `CKSD.Learning.Privacy.LocalEstimation`: lower and upper bounds for local estimation.

The Laplace law and its moments are TauCeti's (`TauCeti.Probability.laplaceMeasure`).
Source: GAPS 107.66.
-/
