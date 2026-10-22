module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem embBit_inter (b : Bool) (X X' : Set Str) :
    embBit b X ∩ embBit b X' = embBit b (X ∩ X') := by
  ext w
  simp only [Set.mem_inter_iff, mem_embBit]
  constructor
  · rintro ⟨⟨w', rfl, hX⟩, w'', heq, hX'⟩
    rw [List.cons.injEq] at heq
    obtain ⟨-, rfl⟩ := heq
    exact ⟨w', rfl, hX, hX'⟩
  · rintro ⟨w', rfl, hX, hX'⟩
    exact ⟨⟨w', rfl, hX⟩, ⟨w', rfl, hX'⟩⟩

end Example62

end DomainTheory.NeighbourhoodSystems
