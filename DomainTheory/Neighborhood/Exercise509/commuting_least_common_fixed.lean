/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise407
public import DomainTheory.Neighborhood.Exercise509.Basic
public import DomainTheory.Neighborhood.Exercise509.commute_apply

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- **Exercise 5.9 (Scott 1981, PRG-19).** Commuting approximable maps have a *least common fixed
point* `x = f(x) = g(x)`. -/
theorem commuting_least_common_fixed {f g : ApproximableMap V V} (hcomm : f.comp g = g.comp f) :
    ∃ x : V.Element, f.toElementMap x = x ∧ g.toElementMap x = x ∧
      ∀ w : V.Element, f.toElementMap w = w → g.toElementMap w = w → x ≤ w := by
  set a := f.fixElement with ha_def
  have hfa : f.toElementMap a = a := toElementMap_fixElement f
  -- `a ⊑ g(a)` since `g(a)` is a fixed point of `f`.
  have ha_le : a ≤ g.toElementMap a := by
    apply fixElement_le_of_toElementMap_le f
    rw [commute_apply hcomm, hfa]
  set x := g.fixAbove ha_le with hx_def
  have hgx : g.toElementMap x = x := fixAbove_isFixed g ha_le
  have hax : a ≤ x := le_fixAbove g ha_le
  -- each `gⁿ(a)` is a fixed point of `f`.
  have hfix_each : ∀ n, f.toElementMap (g.iterFrom a n) = g.iterFrom a n := by
    intro n
    induction n with
    | zero => rw [iterFrom_zero]; exact hfa
    | succ k ih =>
      rw [iterFrom_succ g a k, commute_apply hcomm, ih]
  -- so `f(x) = x` by continuity.
  have hfx : f.toElementMap x = x := by
    apply le_antisymm
    · rw [hx_def, fixAbove, toElementMap_iSupDirected]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [hfix_each n]
      exact NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n
    · rw [hx_def, fixAbove]
      apply NeighborhoodSystem.iSupDirected_le
      intro n
      rw [← hfix_each n]
      exact f.toElementMap_mono (NeighborhoodSystem.le_iSupDirected (g.iterFrom a) _ n)
  refine ⟨x, hfx, hgx, ?_⟩
  intro w hfw hgw
  have haw : a ≤ w := fixElement_le_of_toElementMap_le f (le_of_eq hfw)
  exact fixAbove_least g ha_le haw (le_of_eq hgw)

end ApproximableMap
end DomainTheory.Neighborhood
