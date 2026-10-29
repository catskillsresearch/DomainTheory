module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_7_projection

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

namespace functionSpaceProjection

theorem inclRetrLe {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    ∀ g, functionSpaceInclFun P (functionSpaceRetrFun P g) ≤ g := by
  intro g
  exact ScottMap.le_def.mpr ((proposition_3_7_projection P P).incl_retr_le g)

theorem retrIncl {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    ∀ f, functionSpaceRetrFun P (functionSpaceInclFun P f) = f :=
  (proposition_3_7_projection P P).retr_incl

end functionSpaceProjection

noncomputable def functionSpaceProjection
    {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    IsContinuousLatticeProjection (ScottMap D D) (ScottMap D' D') where
  incl := ⟨functionSpaceInclFun P, functionSpaceInclFun.outer_continuous P⟩
  retr := ⟨functionSpaceRetrFun P, functionSpaceRetrFun.outer_continuous P⟩
  retr_incl := functionSpaceProjection.retrIncl P
  incl_retr_le := functionSpaceProjection.inclRetrLe P

end DomainTheory.ContinuousLattice
