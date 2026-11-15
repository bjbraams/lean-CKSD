module -- shake: keep-all

public import CKSD.Learning.Reinforcement.MarkovDecision
public import CKSD.Learning.Reinforcement.PolicyOptimization

/-!
# Reinforcement learning in finite discounted models

* `CKSD.Learning.Reinforcement.MarkovDecision`: finite discounted Markov decision processes,
  Bellman optimality, resolvent bounds, TD(λ), and asynchronous stochastic approximation
  (GAPS 107.54, 107.58–107.60).
* `CKSD.Learning.Reinforcement.PolicyOptimization`: values of stationary randomized policies,
  the performance-difference identity, and natural policy gradient (GAPS 107.58, 107.61).
-/
