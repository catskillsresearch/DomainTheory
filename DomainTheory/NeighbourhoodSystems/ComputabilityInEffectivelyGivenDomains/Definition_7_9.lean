module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.powerDomain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

/-- Scott's Definition 7.9: the powerdomain and the dagger embedding. -/
theorem definition_79 {α : Type*} (V : NeighborhoodSystem α) :
    (V ≅ᴰ V.dagger) ∧ V.PDmem (V.upSet V.master) :=
  ⟨V.dagger_isomorphic, V.PDmem_master⟩

end DomainTheory.NeighbourhoodSystems
