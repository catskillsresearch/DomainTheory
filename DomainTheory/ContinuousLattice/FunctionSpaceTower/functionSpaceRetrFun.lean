module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun_continuous

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- The retraction part of `[P → P]`, with its underlying function explicit. -/
def functionSpaceRetrFun {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (g : ScottMap D' D') : ScottMap D D :=
  ⟨fun x => P.retr (g (P.incl x)), functionSpaceRetrFun_continuous P g⟩

end DomainTheory.ContinuousLattice
