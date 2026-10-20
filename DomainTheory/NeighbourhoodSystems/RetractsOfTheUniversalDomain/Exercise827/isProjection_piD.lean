module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.isRetraction_piD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.le_idMap_piD

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap
































/-- **Scott's own hint, in full: `Π(d)` is a projection, for every `d`.** -/
theorem isProjection_piD (d : ApproximableMap U U) : IsProjection (piD d) :=
  ⟨isRetraction_piD d, le_idMap_piD d⟩

end DomainTheory.NeighbourhoodSystems
