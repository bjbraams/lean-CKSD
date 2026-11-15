module -- shake: keep-all

public import CKSD.Learning.Bandits.UCB
public import CKSD.Learning.Bandits.Stochastic
public import CKSD.Learning.Bandits.Exp3
public import CKSD.Learning.Bandits.Gittins

/-!
# Bandits

* `CKSD.Learning.Bandits.UCB`: the UCB1 index policy and its regret (GAPS 107.50).
* `CKSD.Learning.Bandits.Stochastic`: stochastic bandits in the reward-table model, regret lower
  bounds, Thompson sampling, minimax regret, and linear bandits (GAPS 107.49, 107.51, 107.62,
  107.63).
* `CKSD.Learning.Bandits.Exp3`: the Exp3 algorithm for adversarial bandits (GAPS 107.52).
* `CKSD.Learning.Bandits.Gittins`: the Gittins index for finite Markov bandits (GAPS 107.51).
-/
