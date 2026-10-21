/-ai
The set of elements way above a fixed element is Scott-open.

The set is an upper set because way-below is monotone on the right. If the supremum of a nonempty directed set lies in it, a witnessing Scott-open neighbourhood of that supremum meets the directed set, and the same neighbourhood witnesses that the fixed element is way below the meeting point.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
import all Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- Auxiliary: the up-set `{z | x ≪ z}` is itself Scott-open. (This is *not* Scott's
Proposition 2.2(vi) — see `wayBelow_self_iff_scottOpen_Ici` for that — but it is a standard
and useful fact, the openness of the sets `↟x`.) -/
theorem scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

end DomainTheory.ContinuousLattice
