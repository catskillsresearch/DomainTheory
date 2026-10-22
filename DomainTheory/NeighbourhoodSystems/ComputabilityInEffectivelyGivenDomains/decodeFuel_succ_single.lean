module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeListBool
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decodeFuel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem decodeFuel_succ_single (fuel c : ℕ) (h : c.unpair.1 = 1) :
    decodeFuel (fuel + 1) c = (decodeListBool c.unpair.2).map (.single ·) := by
  simp [decodeFuel, h]

end Exercise722

end DomainTheory.NeighbourhoodSystems
