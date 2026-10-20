module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piDTypeMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap






















































/-- `piDApply`'s defining formula, restated via `piDType`/`piDTypeMap`. -/
theorem toElementMap_piDApply' (d f : ApproximableMap U U) (t : U.Element) :
    (piDApply d f).toElementMap t =
      (piDType d (subU.toElementMap t)).toElementMap (f.toElementMap (subU.toElementMap t)) := by
  rw [toElementMap_piDApply, piDType, toElementMap_piDTypeMap]

end DomainTheory.NeighbourhoodSystems
