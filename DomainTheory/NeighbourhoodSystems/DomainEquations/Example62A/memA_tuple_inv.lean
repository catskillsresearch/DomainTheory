/-ai
For positive n, if a tagged tuple belongs to MemA, then each of its components belongs to MemA.

Replace the tuple by a variable and case on its membership. The case of the set of all strings would put the empty string in the tuple. In the tuple case, nonemptiness at index zero produces a slot word of the second tuple; transporting it across the equality and applying uniqueness of slot prefixes forces the tags to agree, after which injectivity of embTuple identifies each component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.nil_not_mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- Inversion: the components of a tuple-shaped neighbourhood of `A` are themselves in `A`. -/
theorem memA_tuple_inv (hn : 0 < n) {i : Bool} {X : Fin n → Set Str}
    (h : MemA n (embTuple i X)) : ∀ j, MemA n (X j) := by
  generalize hW : embTuple i X = W at h
  cases h with
  | univ =>
    exfalso
    have : ([] : Str) ∈ embTuple i X := by rw [hW]; exact Set.mem_univ []
    exact nil_not_mem_embTuple this
  | @tuple i' X' hX' =>
    have hne : (embTuple i' X').Nonempty :=
      embTuple_nonempty ⟨0, hn⟩ (memA_nonempty hn (hX' ⟨0, hn⟩))
    rw [← hW] at hne
    obtain ⟨w, j, a, rfl, ha⟩ := hne
    have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' X' := hW ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
    obtain ⟨j', a', he, -⟩ := hmem
    have hii : i = i' := (slotPre_inj he).1
    subst hii
    intro k; rw [embTuple_injective hW k]; exact hX' k

end Example62A

end DomainTheory.NeighbourhoodSystems
