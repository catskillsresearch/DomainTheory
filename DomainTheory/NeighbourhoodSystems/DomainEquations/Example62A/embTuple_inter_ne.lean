/-ai
Tuples with distinct tags have empty intersection.

Extensionality rewrites membership by the tuple characterization. A word in both tuples gives two slot decompositions, and uniqueness of slot prefixes forces the tags to agree.
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

theorem embTuple_inter_ne {i i' : Bool} (h : i ≠ i') (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i' X' = ∅ := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨j, a, rfl, ha⟩ ⟨j', a', heq, ha'⟩
  exact h (slotPre_inj heq).1

end Example62A

end DomainTheory.NeighbourhoodSystems
