module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.toElementMap_piDTypeMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


theorem isFinitaryProjection_piDType (d : ApproximableMap U U) (s : U.Element) :
    FinitaryProjection (piDType d s) := by
  unfold piDType
  rw [toElementMap_piDTypeMap]
  exact isFinitaryProjection_decode_subU (d.toElementMap s)

end DomainTheory.NeighbourhoodSystems
