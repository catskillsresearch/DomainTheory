/-ai
The partial presentation of the neighbourhood system enumerates by the enumeration map onto the carrier, and takes consistency from the recursive decidability of consistency.

The enumeration is the enumeration map. Membership of each enumerated set is the membership characterization applied to the fact that every value of the map lies in the carrier. Surjectivity is the surjectivity of the map, transported along the same characterization. Consistency is the recursive decidability of the consistency relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_surj
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Ssys_cons_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- The partial presentation of `Ssys`: enumeration `SsysX` onto `S`, consistency via
`Ssys_cons_computable`. -/
def SsysPres : ConsistencyPresentation Ssys where
  X := SsysX
  mem_X n := Ssys_mem.mpr (SsysX_mem n)
  surj hY := SsysX_surj (Ssys_mem.mp hY)
  cons_computable := Ssys_cons_computable

end Exercise722

end DomainTheory.NeighbourhoodSystems
