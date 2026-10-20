module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)







theorem he0 : e P 0 = D.master := by
  show P.X (eIdx P 0) = D.master
  rw [eIdx_zero]; exact P.masterIdx_spec

end DomainTheory.NeighbourhoodSystems
