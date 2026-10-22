module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun_continuous

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- The inclusion part of `[P → P]`, with its underlying function explicit. -/
def functionSpaceInclFun {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) : ScottMap D' D' :=
  ⟨fun x => P.incl (f (P.retr x)), functionSpaceInclFun_continuous P f⟩

end DomainTheory.ContinuousLattice
