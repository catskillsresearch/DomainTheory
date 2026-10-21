/-ai
The type map of d sends an element s to j-arrow of sub of d of s.

Unfold the type map and apply the composition law for element maps twice.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


theorem toElementMap_piDTypeMap (d : ApproximableMap U U) (s : U.Element) :
    (piDTypeMap d).toElementMap s = jArrow.toElementMap (subU.toElementMap (d.toElementMap s)) := by
  unfold piDTypeMap
  rw [toElementMap_comp, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
