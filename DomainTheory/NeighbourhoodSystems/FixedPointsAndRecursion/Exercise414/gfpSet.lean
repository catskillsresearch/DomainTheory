/-ai
The greatest fixed point of a monotone endomap f of the power set of a set is the union of the post-fixed points: the set of elements that belong to some set contained in its image under f.
ai-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}

/-- **Exercise 4.14 (Scott 1981, PRG-19).** The *greatest* fixed point of a monotone `f : P A → P A`,
constructed as the union of all post-fixed points `⋃ {x ∣ x ⊆ f(x)}`. -/
def gfpSet (f : Set A → Set A) : Set A := {a | ∃ x : Set A, x ⊆ f x ∧ a ∈ x}

end DomainTheory.NeighbourhoodSystems.Exercise414
