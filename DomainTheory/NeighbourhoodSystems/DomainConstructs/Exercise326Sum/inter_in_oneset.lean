/-ai
The intersection of two truth neighbourhoods, each equal to the master or to the singleton of one, is again the master or the singleton of one.

The four combinations are the master with itself, the master with the singleton in either order, and the singleton with itself, which are the master, the singleton, the singleton, and the singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

theorem inter_in_oneset {C C' : Set Example12.Token} (hc : C = Example12.master ∨ C = Example12.one)
    (hc' : C' = Example12.master ∨ C' = Example12.one) :
    C ∩ C' = Example12.master ∨ C ∩ C' = Example12.one := by
  rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
  · exact Or.inl (Set.inter_self _)
  · exact Or.inr (Set.univ_inter _)
  · exact Or.inr (Set.inter_univ _)
  · exact Or.inr (Set.inter_self _)

end DomainTheory.NeighbourhoodSystems.Exercise326
