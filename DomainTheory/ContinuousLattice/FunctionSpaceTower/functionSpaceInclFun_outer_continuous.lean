module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.functionSpaceInclFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

/-- Continuity, for the lattice Scott topologies on the function spaces, of
`f ↦ i ∘ f ∘ j`. -/
theorem functionSpaceInclFun_outer_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    @Continuous (ScottMap D D) (ScottMap D' D')
      scottTopologicalSpace scottTopologicalSpace (functionSpaceInclFun P) := by
  exact @Continuous.congr (ScottMap D D) (ScottMap D' D')
    scottTopologicalSpace scottTopologicalSpace (conjMap P.incl P.retr).1
    (functionSpaceInclFun P) (conjMap P.incl P.retr).continuous
    (fun f => ScottMap.ext fun _ => rfl)

end DomainTheory.ContinuousLattice
