/-ai
Scott 1976, Theorem 5.4, sum half, expansiveness. If a and b are closures, every set u is contained in the application of their boxed sum to u. Each of the four occupancy cases of (5.13) is expansive: on a one-sided u the shift is expansive and (5.8) rebuilds u, a mixed u goes to the full set, and an empty u is bottom.

By (5.8), u is the square pair of its two components. If both components are empty, that pair is the empty pair and the application is empty. If only the right component is inhabited, the right occupancy value contains the pair because the right shift is expansive and square pairing is monotone, and (5.8) transports the inclusion back to u. The left-only case is symmetric. If both components are inhabited, the application is the full set, which contains every number.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_8
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_mono
public import DomainTheory.DataTypesAsLattices.Closures.squarePair_bot_bot
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 5.4 (sum half), expansiveness.** Each of the four
occupancy cases of (5.13) is expansive: on a one-sided `u` the shift `a'`
is expansive by `boxShift_expansive` and (5.8) rebuilds `u`, while mixed
`u` goes to `⊤` and empty `u` is `⊥`. -/
theorem boxPlus_expansive {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b)
    (u : Pomega) : u ⊆ funOf (boxPlus a b) u := by
  have h8 : squarePair (squareFst u) (squareSnd u) = u := eq_5_8 u
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [hx, hy, squarePair_bot_bot] at h8
    rw [boxPlus_app_empty hx hy, ← h8]
  · rw [boxPlus_app_right hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair botElem (funOf (boxShift b) (squareSnd u)) := by
      rw [hx]
      exact squarePair_mono subset_rfl (boxShift_expansive hb (squareSnd u))
    rwa [h8] at hsub
  · rw [boxPlus_app_left hx hy]
    have hsub : squarePair (squareFst u) (squareSnd u) ⊆
        squarePair (funOf (boxShift a) (squareFst u)) botElem := by
      rw [hy]
      exact squarePair_mono (boxShift_expansive ha (squareFst u)) subset_rfl
    rwa [h8] at hsub
  · rw [boxPlus_app_mixed hx hy]
    exact fun k _ => Set.mem_univ k

end DomainTheory.DataTypesAsLattices
