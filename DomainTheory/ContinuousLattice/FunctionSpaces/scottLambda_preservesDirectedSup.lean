module

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace scottLambda

theorem preservesDirectedSup :
    PreservesDirectedSup
      (scottLambda : ScottMap (D × D') D'' → ScottMap D (ScottMap D' D'')) := by
  intro 𝓕 h𝓕 h𝓕dir
  apply ScottMap.ext
  intro x
  apply ScottMap.ext
  intro y
  rw [apply, ScottMap.sSup_apply, ScottMap.sSup_apply, ScottMap.sSup_apply,
    Set.image_image, Set.image_image]
  congr 1

end scottLambda

end DomainTheory.ContinuousLattice
