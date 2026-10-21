/-ai
The least fixed point of an operator on subsets is the intersection of all pre-fixed points: the set of elements that belong to every subset whose image is contained in the subset.
ai-/
module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** The *least* fixed point of a monotone `f : P A → P A`,
as the intersection of all pre-fixed points `⋂ {x ∣ f(x) ⊆ x}`. -/
def lfpSet (f : Set A → Set A) : Set A := {a | ∀ x : Set A, f x ⊆ x → a ∈ x}

end DomainTheory.NeighbourhoodSystems.Exercise414
