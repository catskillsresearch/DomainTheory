/-ai
The infimum of a Scott-open neighbourhood of an element is way below that element.

The neighbourhood itself is a Scott-open set containing the element and contained in the principal upset of its infimum, because every member of the neighbourhood lies above the infimum.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- The infimum of a Scott-open neighbourhood of `y` is way below `y`: the open set is itself
the required witness. Scott uses this in moving between Definition 2.3 and Proposition 2.4. -/
theorem sInf_wayBelow {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y :=
  ⟨U, hU, hy, fun _ hz => Set.mem_Ici.2 (sInf_le hz)⟩

end DomainTheory.ContinuousLattice
