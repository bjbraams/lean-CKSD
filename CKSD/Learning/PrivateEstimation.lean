module

public import CKSD.Learning.PrivateEstimation.Mechanisms
public import CKSD.Learning.PrivateEstimation.CentralLowerBounds
public import CKSD.Learning.PrivateEstimation.Local


namespace CKSD

/-!
# Private estimation of a bounded mean

Data sets are vectors in `ℝⁿ`, neighbouring when they differ in at most one coordinate. A
central mechanism is a Markov kernel from data sets to real releases. The clipped Laplace
mechanism releases the mean of the data clipped to `[-1,1]` plus Laplace noise of scale
`2 / (n ε)`. Local mechanisms are noninteractive: individual `i` releases `Zᵢ ∼ Qᵢ(· | Xᵢ)`
through an `ε`-locally private kernel to the real line, and an estimator is a measurable
function of the releases. The target is the mean of an unknown law on `[-1,1]` and the risk is
the mean squared error.

The Laplace law and its moments are TauCeti's (`TauCeti.Probability.laplaceMeasure`).
Source: GAPS 107.66.
-/


end CKSD