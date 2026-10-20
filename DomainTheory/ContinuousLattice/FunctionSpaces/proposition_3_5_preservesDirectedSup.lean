module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
import all Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


































/-- `lambda` preserves directed suprema: both sides evaluate, pointwise at `(x, y)`, to
`⊔ {f (x, y) | f ∈ 𝓕}`, since suprema in every function lattice involved are pointwise. -/
theorem proposition_3_5_preservesDirectedSup :
    PreservesDirectedSup
      (scottLambda : ScottMap (D × D') D'' → ScottMap D (ScottMap D' D'')) := by
  intro 𝓕 h𝓕 h𝓕dir
  apply ScottMap.ext
  intro x
  apply ScottMap.ext
  intro y
  rw [scottLambda_apply, ScottMap.sSup_apply, ScottMap.sSup_apply, ScottMap.sSup_apply,
    Set.image_image, Set.image_image]
  congr 1

end DomainTheory.ContinuousLattice
