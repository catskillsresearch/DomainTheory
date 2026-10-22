/-ai
Scott 1972, Proposition 2.2(vi). An element is way below itself if and only if its principal upset is Scott-open.

If the element is way below itself, a witnessing Scott-open neighbourhood contained in the principal upset equals that upset: the upset is contained in the neighbourhood because the neighbourhood is an upper set and contains the element. Conversely, a Scott-open principal upset is a neighbourhood of the element contained in itself.
ai-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


/-- **Scott 1972, Proposition 2.2(vi).** `x ≪ x` iff the principal up-set `{z | x ⊑ z}` (i.e.
`Set.Ici x`) is Scott-open. This characterizes the *compact* (finite, isolated) elements:
`x` is compact exactly when `↑x` is open. -/
theorem wayBelow_self_iff_scottOpen_Ici {x : D} : x ≪ x ↔ ScottOpen (Set.Ici x) := by
  constructor
  · rintro ⟨U, hU, hxU, hsub⟩
    -- `Ici x = U`: `Ici x ⊆ U` since `U` is upper and `x ∈ U`; `U ⊆ Ici x` is `hsub`.
    have hIci : Set.Ici x = U :=
      le_antisymm (fun w hw => hU.1 (Set.mem_Ici.1 hw) hxU) hsub
    rw [hIci]; exact hU
  · intro hopen
    exact ⟨Set.Ici x, hopen, Set.self_mem_Ici, le_refl _⟩

end DomainTheory.ContinuousLattice
