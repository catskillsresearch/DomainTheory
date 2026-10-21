/-ai
Scott 1972, Proposition 2.2(i). The bottom element is way below every element.

The universe is a Scott-open neighbourhood of the element, and every element lies above bottom, so the universe is contained in the principal upset of bottom.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_univ

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.2(i).** `⊥ ≪ x` for every `x`. -/
theorem bot_wayBelow (x : D) : (⊥ : D) ≪ x :=
  ⟨Set.univ, scottOpen_univ, Set.mem_univ x, fun _ _ => bot_le⟩

end DomainTheory.ContinuousLattice
