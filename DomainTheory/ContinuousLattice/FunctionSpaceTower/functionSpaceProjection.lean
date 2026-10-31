module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun
public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceRetrFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.FunctionSpace

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

namespace ContinuousLatticeProjection

theorem functionSpace_inclRetrLe {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : ContinuousLatticeProjection D D') :
    ∀ g, functionSpaceInclFun P (functionSpaceRetrFun P g) ≤ g := by
  intro g
  exact ScottMap.le_def.mpr ((FunctionSpace.projection P P).incl_retr_le g)

theorem functionSpace_retrIncl {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : ContinuousLatticeProjection D D') :
    ∀ f, functionSpaceRetrFun P (functionSpaceInclFun P f) = f :=
  (FunctionSpace.projection P P).retr_incl

noncomputable def functionSpace {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : ContinuousLatticeProjection D D') :
    ContinuousLatticeProjection (ScottMap D D) (ScottMap D' D') where
  incl := ⟨functionSpaceInclFun P, functionSpaceInclFun.outer_continuous P⟩
  retr := ⟨functionSpaceRetrFun P, functionSpaceRetrFun.outer_continuous P⟩
  retr_incl := functionSpace_retrIncl P
  incl_retr_le := functionSpace_inclRetrLe P

end ContinuousLatticeProjection

end DomainTheory.ContinuousLattice
