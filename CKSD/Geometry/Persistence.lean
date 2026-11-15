module -- shake: keep-all

public import CKSD.Geometry.Persistence.Landscapes
public import CKSD.Geometry.Persistence.CechRips
public import CKSD.Geometry.Persistence.Modules
public import CKSD.Geometry.Persistence.RipsStability
public import CKSD.Geometry.Persistence.TopologicalInference
import Mathlib.Geometry.Euclidean.Altitude

/-!
# Persistence and topological inference

Entry module for persistence modules and diagrams, diagram distances and the isometry theorem,
persistence landscapes, Čech and Rips complexes with Gromov–Hausdorff stability of Rips
persistence, the distance to a measure, and topological inference through reach and Morse
persistence. Finite simplicial persistence and matrix reduction are in
`CKSD.Geometry.SimplicialPersistence` and `CKSD.Geometry.MatrixReduction`.
-/
