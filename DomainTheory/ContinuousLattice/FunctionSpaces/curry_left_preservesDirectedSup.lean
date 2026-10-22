/-ai
For a Scott map f on a product and a fixed second coordinate y, the curried map x ↦ f(x, y) preserves directed suprema.

The image of a nonempty directed set S under x ↦ (x, y) is nonempty, and it is directed because a common upper bound c of two indices gives the pair (c, y) above both image pairs. The value of the curried map at the supremum of S is f at the pair (⊔ S, y). That pair is the supremum of the image, the Scott map f preserves the directed supremum of the image, and the image of the curried map is the image of that composite.
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
public import DomainTheory.ContinuousLattice.FunctionSpaces.preservesDirectedSup_coe
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst30
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst33
public import DomainTheory.ContinuousLattice.FunctionSpaces.idMap_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.const_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_prod_mk_right

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- Currying in the `x`-variable: `x ↦ f (x, y)` is Scott-continuous (used for continuity of
`lambda f` as a map `D → [D' → D'']`). -/
theorem curry_left_preservesDirectedSup (f : ScottMap (D × D') D'') (y : D') :
    PreservesDirectedSup (fun x => f (x, y)) := by
  intro S hS hSdir
  have hS' : DirectedOn (· ≤ ·) (Set.image (fun x => (x, y)) S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨(c, y), Set.mem_image_of_mem _ hc, And.intro (And.intro hac le_rfl) (And.intro hbc le_rfl)⟩
  have hS'ne : (Set.image (fun x => (x, y)) S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨(s, y), s, hs, rfl⟩
  rw [show (fun x => f (x, y)) (sSup S) = f (sSup S, y) from rfl,
    ← sSup_image_prod_mk_right y S hS,
    f.preservesDirectedSup_coe (Set.image (fun x => (x, y)) S) hS'ne hS']
  congr 1
  simp [Set.image_image]

end DomainTheory.ContinuousLattice
