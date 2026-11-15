module -- shake: keep-all

public import CKSD.Learning.Algorithms
public import CKSD.Learning.Generalization
public import CKSD.Learning.Approximation
public import CKSD.Learning.Networks
public import CKSD.Learning.Networks.GaussianLimit
public import CKSD.Learning.Models
public import CKSD.Learning.KernelAndClustering
public import CKSD.Learning.LocalAveraging
public import CKSD.Learning.GraphicalModels
public import CKSD.Learning.RandomGraphs
public import CKSD.Learning.RandomGraphs.Connectivity
public import CKSD.Learning.RandomGraphs.ConnectivityThreshold
public import CKSD.Learning.RandomGraphs.Subcritical
public import CKSD.Learning.Bandits
public import CKSD.Learning.Reinforcement
public import CKSD.Learning.Privacy

/-!
# Section 107: Statistical learning

Entry module for the CKSD formalization of Section 107 of the catalogue (statistical learning
theory, online learning and bandits, reinforcement learning, graphical models, privacy, and
learning models).

## Contents

* `CKSD.Learning.Basic`: shared definitions (Rademacher complexity, classification risk, Hedge
  weights, differential privacy, bandit play counts).
* `CKSD.Learning.Generalization`: concentration and Rademacher bounds, contraction, the margin
  bound, exponential weights, conformal coverage, classification lower bounds, and uniform
  stability.
* `CKSD.Learning.Approximation`, `CKSD.Learning.Networks`, `CKSD.Learning.Models`: approximation
  by networks, network complexity and wide-network limits, log partition functions and least
  squares.
* `CKSD.Learning.KernelAndClustering`, `CKSD.Learning.LocalAveraging`: kernel ridge regression,
  `k`-means, and nearest-neighbour rules.
* `CKSD.Learning.GraphicalModels` and its submodules: partial sums over coordinates of finite
  configurations, pairwise graphical models, belief propagation, chordal graphs, and junction
  trees.
* `CKSD.Learning.RandomGraphs` and its submodules: the two-group stochastic block model with its
  exact-recovery, weak-recovery, and contiguity thresholds; components, the giant component, and
  the connectivity threshold of binomial random graphs; and exchangeable random graphs.
* `CKSD.Learning.Bandits` and its submodules: UCB1, stochastic and linear bandits, Exp3, and
  the Gittins index.
* `CKSD.Learning.Algorithms`: empirical risk, margin and exponential losses, AdaBoost, simple
  neural predictors, the `k`-means distortion, and the AboveThreshold mechanism.
* `CKSD.Learning.Reinforcement` and its submodules: Markov decision processes, temporal
  difference learning, and policy optimization.
* `CKSD.Learning.Privacy` and its submodules: differential privacy and private estimation.
-/
