module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_subset {b : Bool} {X X' : Set Str} :
    embBit b X ⊆ embBit b X' ↔ X ⊆ X' := by
  constructor
  · intro h w' hw'
    obtain ⟨w'', heq, hX'⟩ := h ⟨w', rfl, hw'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact hX'
  · rintro h w ⟨w', rfl, hX⟩
    exact ⟨w', rfl, h hX⟩

end Example62

end DomainTheory.NeighbourhoodSystems
