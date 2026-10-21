/-ai
If some component of a tagged tuple is nonempty, then the tuple is nonempty.

Prefix a witness from that component by the slot prefix of its index.
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

theorem embTuple_nonempty {i : Bool} {X : Fin n → Set Str} (j : Fin n) (h : (X j).Nonempty) :
    (embTuple i X).Nonempty := by
  obtain ⟨a, ha⟩ := h
  exact ⟨slotPre i (j : ℕ) ++ a, j, a, rfl, ha⟩

end Example62A

end DomainTheory.NeighbourhoodSystems
