/-ai
Tarski's operator on subsets of the domain sends a set to the complement of the range of the second injection, united with the image under that injection of the image of the set under the first injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise424

open DomainTheory.NeighbourhoodSystems.Exercise414 Function

variable {A B : Type*} {f : A → B} {g : B → A}

/-- Tarski's operator `T(X) = (A − g(B)) ∪ g(f(X))` on `P A`. -/
def sbOp (f : A → B) (g : B → A) (X : Set A) : Set A := (Set.range g)ᶜ ∪ g '' (f '' X)

end DomainTheory.NeighbourhoodSystems.Exercise424
