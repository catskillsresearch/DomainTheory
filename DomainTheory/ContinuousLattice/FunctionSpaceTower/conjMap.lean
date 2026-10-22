module

public import DomainTheory.ContinuousLattice.FunctionSpaceTower.conjMap_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

attribute [instance] CLat.str

section Conj

open Set

variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]

/-- Conjugation `f ↦ post ∘ f ∘ pre` as a Scott map `[Y → Y] → [W → Z]`. -/
noncomputable def conjMap (post : ScottMap Y Z) (pre : ScottMap W Y) :
    ScottMap (ScottMap Y Y) (ScottMap W Z) :=
  ⟨conjMapFun post pre, continuous_of_preservesDirectedSup (conjMap_preservesDirectedSup post pre)⟩

end Conj

end DomainTheory.ContinuousLattice
