module

public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Data.Finset.Basic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- A basis witnesses the continuous-lattice property by way-below elements. -/
class ContinuousBasis {α : Type u} [CompleteLattice α]
    (basis : α → Set α) : Prop where
  out : ∀ x, @DirectedSet α completeLatticePreorder (basis x) ∧
    (∀ y ∈ basis x, WayBelow y x) ∧
    x = @sSup α completeLatticeSupSet (basis x)

end DomainTheory.DataTypesAsLattices
