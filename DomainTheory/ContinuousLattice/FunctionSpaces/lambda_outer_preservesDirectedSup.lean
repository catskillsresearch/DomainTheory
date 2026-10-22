/-ai
For a Scott map f from a product D × D' into D'', the map sending x to the Scott map y ↦ f(x, y) preserves directed suprema. Equality in the function space is pointwise and reduces to preservation by the other curry.

At a point y, extensionality leaves f of the pair whose first coordinate is the supremum of the directed set. The pointwise formula for suprema of Scott maps rewrites the other side, and preservation of directed suprema by the curry in the left variable identifies the two sides.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambdaAt
public import DomainTheory.ContinuousLattice.FunctionSpaces.curry_left_preservesDirectedSup

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- The outer half of currying: `x ↦ (y ↦ f (x, y))` preserves directed suprema (so `lambda f` is a
Scott map `D → [D' → D'']`). Equality in `[D' → D'']` is pointwise, reducing to `curry_left`. -/
theorem lambda_outer_preservesDirectedSup (f : ScottMap (D × D') D'') :
    PreservesDirectedSup (fun x => scottLambdaAt f x) := by
  intro S hS hSdir
  apply ScottMap.ext
  intro y
  show f (sSup S, y)
      = ((sSup (Set.image (fun x => scottLambdaAt f x) S) : ScottMap D' D'') : D' → D'') y
  rw [ScottMap.sSup_apply, Set.image_image]
  exact curry_left_preservesDirectedSup f y hS hSdir

end DomainTheory.ContinuousLattice
