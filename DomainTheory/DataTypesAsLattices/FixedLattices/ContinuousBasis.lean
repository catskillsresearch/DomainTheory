/-ai
A set-valued map on a complete lattice is a continuous basis when, for every element x, the set assigned to x is directed, every member of that set is way-below x, and x equals the supremum of that set. Such a basis witnesses the continuous-lattice property by way-below elements.
ai-/
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
