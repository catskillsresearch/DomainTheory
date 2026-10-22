/-ai
In a continuous lattice, a Scott-open set containing z contains the whole principal upset of some element way below z.

The set of elements way below z is nonempty, because bottom is way below z, and its supremum equals z, hence lies in the open set. Directedness and Scott-openness supply an element of that set already in the open set. The open set is an upper set, so the principal upset of this element is contained in it.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic
public import DomainTheory.ContinuousLattice.WayBelow.bot_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- A strengthening of `exists_wayBelow_subset`: the witness `a ≪ z` can be taken with the whole
principal up-set `Set.Ici a` (not merely `↟a`) inside `U`. The element `a` produced lies in the
open `U`, which is upper, so `↑a ⊆ U`. -/
theorem exists_wayBelow_Ici_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ Set.Ici a ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 (Set.mem_Ici.1 hw) haU⟩

end DomainTheory.ContinuousLattice
