/-ai
The intersection of two rational-interval neighbourhoods with a point in common is again a rational-interval neighbourhood.

If either set is the whole real line, the intersection is the other neighbourhood. If both are open intervals with rational endpoints, the shared point gives a strict inequality from each left endpoint to the opposite right endpoint. The maximum of the left endpoints is therefore strictly below the minimum of the right endpoints. The intersection of the two intervals equals the open interval between that maximum and that minimum, whose endpoints are rational.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import all Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- **Exercise 1.17 — intersections.** The intersection of two neighbourhoods that share a point
is again a neighbourhood: `Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d)`, with rational endpoints,
non-empty because it contains the shared point. -/
theorem inter_mem' {X Y : Set ℝ} (hX : ratIntervalMem X) (hY : ratIntervalMem Y)
    (hne : (X ∩ Y).Nonempty) : ratIntervalMem (X ∩ Y) := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · rw [Set.univ_inter]; exact hY
  · rcases hY with rfl | ⟨c, d, hcd, rfl⟩
    · rw [Set.inter_univ]; exact Or.inr ⟨a, b, hab, rfl⟩
    · obtain ⟨z, ⟨hza, hzb⟩, hzc, hzd⟩ := hne
      have had : a < d := by exact_mod_cast hza.trans hzd
      have hcb : c < b := by exact_mod_cast hzc.trans hzb
      have hlt : max a c < min b d := by
        simp only [max_lt_iff, lt_min_iff]
        exact ⟨⟨hab, hcb⟩, had, hcd⟩
      have hset : Set.Ioo (a : ℝ) b ∩ Set.Ioo (c : ℝ) d
          = Set.Ioo ((max a c : ℚ) : ℝ) ((min b d : ℚ) : ℝ) := by
        rw [Set.Ioo_inter_Ioo, Rat.cast_max, Rat.cast_min]
      exact Or.inr ⟨max a c, min b d, hlt, hset⟩

end RatInterval

end DomainTheory.NeighbourhoodSystems
