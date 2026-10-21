/-ai
The empty string does not lie in a tagged tuple.

A membership witness equates the empty string with the cons of the tag onto a slot body, and a cons is never empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem nil_not_mem_embTuple {i : Bool} {X : Fin n → Set Str} : ([] : Str) ∉ embTuple i X := by
  rintro ⟨j, a, heq, -⟩
  rw [slotPre, List.cons_append] at heq
  exact List.cons_ne_nil _ _ heq.symm

end Example62A

end DomainTheory.NeighbourhoodSystems
