/-ai
A set is a neighbourhood of the unary sequence system if and only if it is a tail or a singleton.

The equivalence holds by definition.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.mem_tail
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.memC1
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise425.C1

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

@[simp] theorem C1_mem {X : Set ℕ} : C1.mem X ↔ memC1 X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise425
