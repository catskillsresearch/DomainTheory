/-ai
The Tarski fixed set is the least fixed point of Tarski's operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise424.sbOp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- The Tarski fixed point `X` with `X = (A − g(B)) ∪ g(f(X))` (`lfpSet`, Exercise 4.14). -/
def sbSet (f : A → B) (g : B → A) : Set A := lfpSet (sbOp f g)

end DomainTheory.NeighbourhoodSystems.Exercise424
