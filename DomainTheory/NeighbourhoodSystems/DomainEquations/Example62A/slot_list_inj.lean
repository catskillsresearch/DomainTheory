/-ai
If two strings, each a block of ones followed by false and a remainder, are equal, then the lengths of the blocks and the remainders agree.

Induction on the two lengths. Both zero simplifies to equality of the remainders. A zero against a successor, or a successor against a zero, is contradictory after unfolding one replicate. When both are successors, cancel one leading true and apply the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

/-- Parsing the `1ʲ0` body: the position of the first `false` pins down `j` and the remainder. -/
theorem slot_list_inj : ∀ (j j' : ℕ) (u v : Str),
    List.replicate j true ++ false :: u = List.replicate j' true ++ false :: v → j = j' ∧ u = v
  | 0, 0, u, v, h => by simpa using h
  | 0, j' + 1, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, 0, u, v, h => by simp [List.replicate_succ] at h
  | j + 1, j' + 1, u, v, h => by
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append,
        List.cons.injEq] at h
      obtain ⟨hj, hu⟩ := slot_list_inj j j' u v h.2
      exact ⟨by rw [hj], hu⟩

end Example62A

end DomainTheory.NeighbourhoodSystems
