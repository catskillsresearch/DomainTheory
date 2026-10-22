module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion_spec

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.UnionClosed
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `Vunion_spec`, repackaged to accept (and discard) `IsComputableUnion`'s hypothesis. -/
theorem Vunion_spec' {n m : ℕ} (_ : ∃ k, VX k = VX n ∪ VX m) : VX (Vunion n m) = VX n ∪ VX m :=
  Vunion_spec n m

end DomainTheory.NeighbourhoodSystems
