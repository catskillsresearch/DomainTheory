module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u
attribute [instance] CLat.str

namespace functionSpaceInclFun

/-- Continuity of the inner map `i ∘ f ∘ j`. -/
theorem continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) :
    @Continuous D' D' scottTopologicalSpace scottTopologicalSpace
      (fun x => P.incl (f (P.retr x))) :=
  @Continuous.congr D' D' scottTopologicalSpace scottTopologicalSpace
    (P.incl.comp (f.comp P.retr)).1 (fun x => P.incl (f (P.retr x)))
    (P.incl.comp (f.comp P.retr)).continuous (fun _ => rfl)

end functionSpaceInclFun

/-- The inclusion part of `[P → P]`, with its underlying function explicit. -/
def functionSpaceInclFun {D D' : Type u} [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') (f : ScottMap D D) : ScottMap D' D' :=
  ⟨fun x => P.incl (f (P.retr x)), functionSpaceInclFun.continuous P f⟩

namespace functionSpaceInclFun

/-- Continuity, for the lattice Scott topologies on the function spaces, of
`f ↦ i ∘ f ∘ j`. -/
theorem outer_continuous {D D' : Type u}
    [CompleteLattice D] [CompleteLattice D']
    (P : IsContinuousLatticeProjection D D') :
    @Continuous (ScottMap D D) (ScottMap D' D')
      scottTopologicalSpace scottTopologicalSpace (functionSpaceInclFun P) := by
  exact @Continuous.congr (ScottMap D D) (ScottMap D' D')
    scottTopologicalSpace scottTopologicalSpace (conjMap P.incl P.retr).1
    (functionSpaceInclFun P) (conjMap P.incl P.retr).continuous
    (fun f => ScottMap.ext fun _ => rfl)

end functionSpaceInclFun

end DomainTheory.ContinuousLattice
