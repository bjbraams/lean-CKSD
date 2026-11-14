module

public import CKSD.Learning.MarginsAndBandits
public import CKSD.Learning.Algorithms
public import CKSD.Learning.CoordinateSum
public import CKSD.Learning.GraphicalModels
public import CKSD.Learning.BeliefPropagationTree
public import CKSD.Learning.KernelAndClustering
public import CKSD.Learning.Approximation
public import CKSD.Learning.Generalization
public import CKSD.Learning.Models
public import CKSD.Learning.UCBAnalysis
public import CKSD.Learning.MarkovDecision
public import CKSD.Learning.Privacy
public import CKSD.Learning.LocalAveraging
public import CKSD.Learning.JunctionTree
public import CKSD.Learning.Networks
public import CKSD.Learning.Networks.GaussianLimit
public import CKSD.Learning.RandomGraphs
public import CKSD.Learning.RandomGraphs.Connectivity
public import CKSD.Learning.RandomGraphs.ConnectivityThreshold
public import CKSD.Learning.RandomGraphs.Subcritical
public import CKSD.Learning.Bandits
public import CKSD.Learning.Policies
public import CKSD.Learning.ChordalGraphs
public import CKSD.Learning.PrivateEstimation

/-!
# Section 107: Statistical learning

Entry module for the CKSD formalization of Section 107 of the catalogue (statistical learning
theory, online learning and bandits, reinforcement learning, graphical models, privacy, and
learning models).

## Contents

* `CKSD.Learning.Basic`: shared definitions (Rademacher complexity, classification risk, Hedge
  weights, differential privacy, bandit play counts).
* `CKSD.Learning.Generalization`: concentration and Rademacher bounds, contraction, exponential
  weights, conformal coverage, classification lower bounds, and uniform stability.
* `CKSD.Learning.Approximation`, `CKSD.Learning.Networks`, `CKSD.Learning.Models`: approximation
  by networks, network complexity and wide-network limits, log partition functions and least
  squares.
* `CKSD.Learning.KernelAndClustering`, `CKSD.Learning.LocalAveraging`: kernel ridge regression,
  `k`-means, and nearest-neighbour rules.
* `CKSD.Learning.CoordinateSum`: partial sums of functions of finite configurations over sets
  of coordinates.
* `CKSD.Learning.GraphicalModels`, `CKSD.Learning.BeliefPropagationTree`,
  `CKSD.Learning.JunctionTree`, `CKSD.Learning.ChordalGraphs`: pairwise graphical models,
  belief propagation, chordal graphs, and junction trees.
* `CKSD.Learning.RandomGraphs` and its submodules: the two-group stochastic block model with its
  exact-recovery, weak-recovery, and contiguity thresholds; components, the giant component, and
  the connectivity threshold of binomial random graphs; and exchangeable random graphs.
* `CKSD.Learning.UCBAnalysis`, `CKSD.Learning.Bandits`, `CKSD.Learning.MarginsAndBandits`:
  bandit and online-learning algorithms and their regret.
* `CKSD.Learning.Algorithms`: empirical risk, margin and exponential losses, AdaBoost, simple
  neural predictors, the `k`-means distortion, and the AboveThreshold mechanism.
* `CKSD.Learning.MarkovDecision`, `CKSD.Learning.Policies`: Markov decision processes, temporal
  difference learning, and policy optimization.
* `CKSD.Learning.Privacy`, `CKSD.Learning.PrivateEstimation`: differential privacy and private
  estimation.
-/
