/-ai
Every element of the final-segment system on the natural numbers is either a finite element or the single limit element.

Classically, either every tail belongs to the element, or some tail does not. In the first case the element equals the limit: a neighbourhood of the element is a neighbourhood of the system, and every neighbourhood is a tail, which belongs to the element. In the second case the least failing index, found by search, is positive, because the master belongs to the element, and every smaller index belongs to the element by minimality. The element then equals the finite element one below that index. A tail belongs to the element exactly when its index is at most that predecessor: a larger index would carry the failing tail into the element by upward closure along the inclusion of tails, while a strictly smaller index belongs by minimality. An arbitrary neighbourhood of the element is a tail satisfying that bound, and a neighbourhood contained in such a tail belongs to the element by the same equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise112.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Exercise 1.12 (classification).** Every element is either a finite element `fin n` or the
single limit element `top`. *Classical*: it decides whether the indices present in `x` are bounded.
(Hint realized: "there is only one limit element.") -/
theorem element_eq (x : neighborhoodSystem.Element) :
    (∃ n, x = fin n) ∨ x = top := by
  classical
  by_cases h : ∀ n, x.mem (tail n)
  · refine Or.inr ?_
    apply Element.ext
    intro X
    constructor
    · intro hx; exact x.sub hx
    · rintro ⟨n, rfl⟩; exact h n
  · refine Or.inl ?_
    have h' : ∃ n, ¬ x.mem (tail n) := not_forall.mp h
    have hpos : ∀ n, ¬ x.mem (tail n) → 0 < n := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact absurd x.master_mem hn
      · exact hp
    have hspec : ¬ x.mem (tail (Nat.find h')) := Nat.find_spec h'
    have hmin : ∀ j, j < Nat.find h' → x.mem (tail j) := by
      intro j hj
      by_contra hc
      exact Nat.find_min h' hj hc
    have hn₀ : 0 < Nat.find h' := hpos _ hspec
    refine ⟨Nat.find h' - 1, ?_⟩
    apply Element.ext
    intro X
    have key : ∀ j, x.mem (tail j) ↔ j ≤ Nat.find h' - 1 := by
      intro j
      constructor
      · intro hj
        by_contra hc
        have hle : Nat.find h' ≤ j := by omega
        exact hspec (x.up_mem hj (mem_tail_nbhd (Nat.find h')) (tail_subset_iff.mpr hle))
      · intro hj
        exact hmin j (by omega)
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := x.sub hx
      exact ⟨mem_tail_nbhd j, tail_subset_iff.mpr ((key j).mp hx)⟩
    · rintro ⟨hX, hsub⟩
      obtain ⟨j, rfl⟩ := hX
      exact (key j).mpr (tail_subset_iff.mp hsub)

end DomainTheory.NeighbourhoodSystems.Exercise112
