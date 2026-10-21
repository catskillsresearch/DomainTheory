/-ai
One tagged tuple is contained in another with the same tag if and only if every component is contained in the corresponding component.

In the forward direction, prefix a component element and send it into the larger tuple; uniqueness of slot prefixes recovers the index and the remainder. In the reverse direction, a slot witness of the smaller tuple stays in the same slot of the larger tuple by the component inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem embTuple_subset {i : Bool} {X X' : Fin n → Set Str} :
    embTuple i X ⊆ embTuple i X' ↔ ∀ j, X j ⊆ X' j := by
  constructor
  · intro h j a ha
    obtain ⟨j', a', heq, ha'⟩ := h ⟨j, a, rfl, ha⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ha'
  · rintro h w ⟨j, a, rfl, ha⟩
    exact ⟨j, a, rfl, h j ha⟩

end Example62A

end DomainTheory.NeighbourhoodSystems
