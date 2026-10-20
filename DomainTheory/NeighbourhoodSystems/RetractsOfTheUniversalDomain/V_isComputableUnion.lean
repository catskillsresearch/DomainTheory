module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.primrec_Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.V_union_computable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`V` has a computable `∪`.** -/
def V_isComputableUnion : IsComputableUnion VComputablePresentation where
  unionIdx := Vunion
  unionIdx_primrec := primrec_Vunion
  unionIdx_spec := Vunion_spec'
  union_computable := V_union_computable

end DomainTheory.NeighbourhoodSystems
