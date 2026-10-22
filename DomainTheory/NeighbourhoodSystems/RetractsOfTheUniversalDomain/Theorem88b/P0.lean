module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_involutive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_primrec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The re-pointed presentation `P₀`**: `P`'s enumeration reindexed by `eIdx`, so that
`P₀.X 0 = D.master`. Built via `ComputablePresentation.reindexInvolutive`, so every one of Scott's
structural fields — in particular the two deciders `interEq_computable`/`cons_computable` needed
for `DAtom_recDecidable` — transfers automatically, with no need to redo Part 5's work. -/
noncomputable def P0 : ComputablePresentation D :=
  P.reindexInvolutive (eIdx P) (eIdx_involutive P) (eIdx_primrec P)

end DomainTheory.NeighbourhoodSystems
