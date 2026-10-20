module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_ne {b b' : Bool} (h : b ≠ b') {X Y : Set Str} (hX : X.Nonempty) :
    embBit b X ≠ embBit b' Y := by
  intro heq
  obtain ⟨w', hw'⟩ := hX
  have hmem : (b :: w') ∈ embBit b' Y := heq ▸ (⟨w', rfl, hw'⟩ : (b :: w') ∈ embBit b X)
  obtain ⟨w'', he, -⟩ := hmem
  rw [List.cons.injEq] at he
  exact h he.1

end Example62

end DomainTheory.NeighbourhoodSystems
