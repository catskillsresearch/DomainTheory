module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embT

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem toBB_fromBB (s : BB.Element) : toBB (fromBB s) = s := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact s.master_mem
    · exact (fromBB_mem_embF hX).mp hs
    · exact (fromBB_mem_embT hY).mp hs
  · intro hW
    rcases s.sub hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (fromBB_mem_embF hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (fromBB_mem_embT hY).mpr hW⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
