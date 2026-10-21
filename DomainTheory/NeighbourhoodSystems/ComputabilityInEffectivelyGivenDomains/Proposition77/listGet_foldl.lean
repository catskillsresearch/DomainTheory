/-ai
Folding the indexing step from the pair of c plus one and a default value returns the defaulted c-th entry of the list.

On the empty list both sides are the default. On a cons, the step decrements the countdown. If the index is zero, the countdown one selects the head. If the index is positive, it is a successor, the countdown is not one, the value is carried, and the inductive hypothesis reads the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp_pair
import all DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_foldl_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The fold reads off the `cd-1`-th element (default `val`). -/
theorem listGet_foldl (l : List ℕ) (c val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0)))
        (Nat.pair (c + 1) val) l).unpair.2 = l.getD c val := by
  induction l generalizing c val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · rw [show isOne (0 + 1) = 1 from rfl, selectFn_one, listGet_foldl_zero,
          List.getD_cons_zero]
      · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [show isOne (c' + 1 + 1) = 0 by unfold isOne; omega, selectFn_zero, ih,
          List.getD_cons_succ]

end Proposition77

end DomainTheory.NeighbourhoodSystems
