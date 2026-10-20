module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.fromBB_mem_embT

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem fromBB_toBB (x : B.Element) : fromBB (toBB x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨X, hX, rfl, hs⟩ | ⟨Y, hY, rfl, hs⟩)
    · exact x.master_mem
    · exact (toBB_mem_inj₀ hX).mp hs
    · exact (toBB_mem_inj₁ hY).mp hs
  · intro hW
    rcases memB_cases (x.sub hW) with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl, (toBB_mem_inj₀ hX).mpr hW⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl, (toBB_mem_inj₁ hY).mpr hW⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
