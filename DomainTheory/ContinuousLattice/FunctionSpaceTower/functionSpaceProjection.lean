module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun_outer_continuous
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrIncl
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclRetrLe

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- Scott's Proposition 3.7 construction specialized diagonally. -/
noncomputable def functionSpaceProjection
    {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    IsContinuousLatticeProjection (ScottMap D D) (ScottMap D' D') where
  incl := ⟨functionSpaceInclFun P, functionSpaceInclFun_outer_continuous P⟩
  retr := ⟨functionSpaceRetrFun P, functionSpaceRetrFun_outer_continuous P⟩
  retr_incl := functionSpaceRetrIncl P
  incl_retr_le := functionSpaceInclRetrLe P

end DomainTheory.ContinuousLattice
