/-ai
The intersection of two tuples with the same tag is the tuple of the componentwise intersections.

Extensionality rewrites membership by the tuple characterization. Two witnesses in the intersection have prefixes identified by uniqueness of slot prefixes, so the indices agree and the common remainder lies in both components. A witness in the componentwise intersection belongs to both tuples.
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

theorem embTuple_inter {i : Bool} (X X' : Fin n → Set Str) :
    embTuple i X ∩ embTuple i X' = embTuple i (fun j => X j ∩ X' j) := by
  ext w
  simp only [Set.mem_inter_iff, mem_embTuple]
  constructor
  · rintro ⟨⟨j, a, rfl, ha⟩, ⟨j', a', heq, ha'⟩⟩
    obtain ⟨-, hjj, rfl⟩ := slotPre_inj heq
    obtain rfl : j = j' := Fin.ext hjj
    exact ⟨j, a, rfl, ha, ha'⟩
  · rintro ⟨j, a, rfl, ha, ha'⟩
    exact ⟨⟨j, a, rfl, ha⟩, ⟨j, a, rfl, ha'⟩⟩

end Example62A

end DomainTheory.NeighbourhoodSystems
