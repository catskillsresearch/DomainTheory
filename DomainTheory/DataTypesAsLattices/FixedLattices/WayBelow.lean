/-ai
An element x of a complete lattice is way-below an element y when every directed set whose supremum lies above y has some member lying above x. The relation is phrased using directed suprema.
ai-/
module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeLE
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticeSupSet
public import DomainTheory.DataTypesAsLattices.FixedLattices.completeLatticePreorder

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The way-below relation, phrased using directed suprema. -/
def WayBelow {α : Type u} [CompleteLattice α] (x y : α) : Prop :=
  ∀ s : Set α, @DirectedSet α completeLatticePreorder s →
    @LE.le α completeLatticeLE y (@sSup α completeLatticeSupSet s) →
    ∃ z ∈ s, @LE.le α completeLatticeLE x z

end DomainTheory.DataTypesAsLattices
