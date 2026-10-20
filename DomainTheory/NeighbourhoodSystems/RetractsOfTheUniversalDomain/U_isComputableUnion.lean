module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion_primrec
  unionIdx_spec := Uunion_spec
  union_computable := U_union_computable

end DomainTheory.NeighbourhoodSystems
