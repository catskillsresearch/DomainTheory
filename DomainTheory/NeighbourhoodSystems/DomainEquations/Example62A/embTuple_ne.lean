module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.slotPre_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

theorem embTuple_ne {i i' : Bool} (h : i ≠ i') {X Y : Fin n → Set Str} (j : Fin n)
    (hX : (X j).Nonempty) : embTuple i X ≠ embTuple i' Y := by
  intro heq
  obtain ⟨a, ha⟩ := hX
  have hmem : slotPre i (j : ℕ) ++ a ∈ embTuple i' Y := heq ▸ (⟨j, a, rfl, ha⟩ : _ ∈ embTuple i X)
  obtain ⟨j', a', he, -⟩ := hmem
  exact h (slotPre_inj he).1

end Example62A

end DomainTheory.NeighbourhoodSystems
