module

public import CKSD.LinearModels.DirectedGraphical.Basic
public import CKSD.LinearModels.DirectedGraphical.Interventions
public import CKSD.LinearModels.DirectedGraphical.Markov
public import CKSD.LinearModels.DirectedGraphical.DoCalculus
public import CKSD.LinearModels.DirectedGraphical.Discovery

/-!
# Directed Markov properties, interventions, and causal discovery for discrete variables

All variables take values in one finite state type `S`, and a law on the configurations
`V → S` is given by a probability mass function. Marginal and conditional probabilities are
finite sums and quotients, with Lean's convention `x / 0 = 0`; whenever a conditional
probability appears in a formula, the conditioning event is assumed to have positive
probability. The graph-theoretic notions (`CausalGraph`, active paths, d-separation, skeleton,
unshielded colliders, truncated factorization) are those of `CKSD.LinearModels.DirectedGraphical.Basic.CausalGraph`.

A single configuration `b : V → S` carries the values of all variables that appear in a query;
for disjoint vertex sets `X`, `Y`, `Z` the values `x`, `y`, `z` are its restrictions.
Sums over the values of a set `B` of variables run over `B → S` and overwrite `b` on `B`.

Sources: GAPS 105.62, 105.63, 105.64, and 105.70 (discrete-variable forms).

The central step is `condIndepMass_directedFactorizationMass_of_dSeparated`: a recursive product
of local masses satisfies the global directed Markov property. Its proof follows Lauritzen
(*Graphical Models*, 1996, §3.2): the coordinates outside the ancestral closure of
`A ∪ B ∪ C` are summed out, and the remaining product splits into a factor depending on the
vertices reachable from `A` by trails whose noncolliders avoid `C` and whose colliders lie in
that ancestral closure, and a factor depending on the other vertices; the graph-theoretic
steps are in `CKSD.LinearModels.DirectedGraphical.Basic.ActiveTrails`. The rules of the do-calculus are derived from it:
rule 1 directly, rule 2 by comparing with the mass in which the children of `Z` read fixed
values of `Z`, and rule 3 by Pearl's augmentation of the graph with an intervention indicator
(Pearl, *Causality*, 2009, §3.4). The back-door and front-door formulae follow from rule 2 and
the invariance of the marginal law of nondescendants under intervention.
-/
