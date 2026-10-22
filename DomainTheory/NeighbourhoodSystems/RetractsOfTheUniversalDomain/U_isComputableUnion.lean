module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_primrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion_spec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.U_union_computable

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`U` has a computable `∪`.** -/
def U_isComputableUnion : IsComputableUnion UComputablePresentation where
  unionIdx := Uunion
  unionIdx_primrec := Uunion_primrec
  unionIdx_spec := Uunion_spec
  union_computable := U_union_computable

end DomainTheory.NeighbourhoodSystems
