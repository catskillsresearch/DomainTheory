module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slot_list_inj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

/-- **Uniqueness of slot decomposition.** A token `i 1ʲ 0 u` determines the tag `i`, the index `j`,
and the remainder `u`. This is what makes the slots pairwise disjoint. -/
theorem slotPre_inj {i i' : Bool} {j j' : ℕ} {u v : Str}
    (h : slotPre i j ++ u = slotPre i' j' ++ v) : i = i' ∧ j = j' ∧ u = v := by
  rw [slotPre, slotPre, List.cons_append, List.cons_append, List.cons.injEq] at h
  obtain ⟨hi, hrest⟩ := h
  rw [List.append_assoc, List.append_assoc, List.singleton_append, List.singleton_append] at hrest
  obtain ⟨hj, huv⟩ := slot_list_inj j j' u v hrest
  exact ⟨hi, hj, huv⟩

end Example62A

end DomainTheory.NeighbourhoodSystems
