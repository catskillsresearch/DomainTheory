/-ai
For positive n, every set in MemA is nonempty.

Induction on the membership. The set of all strings contains the empty string. A tagged tuple is nonempty by embTuple_nonempty at index zero, using the inductive hypothesis on that component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_nonempty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- Under `0 < n` every neighbourhood of `A` is non-empty (Scott's `∅ ∉ A`). -/
theorem memA_nonempty (hn : 0 < n) : ∀ {W}, MemA n W → W.Nonempty := by
  intro W hW
  induction hW with
  | univ => exact ⟨[], Set.mem_univ []⟩
  | tuple i hX ih => exact embTuple_nonempty ⟨0, hn⟩ (ih ⟨0, hn⟩)

end Example62A

end DomainTheory.NeighbourhoodSystems
