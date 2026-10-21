/-ai
Every pair in the decoded canonical list of a code has first component at least zero and second component at most one.

Unfold the canonical code. If the canonical list code is zero, the zero test selects the master code, whose decoded list is a singleton, and the bounds are numerical. If it is not zero, the zero test equals zero: a contradictory positive value, together with the bound of the zero test by one, would force the code to be zero. Selection is then the canonical list itself. Membership in its decoded list supplies the pair, and the two bounds are the right-hand supremum inequality and the right-hand infimum inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Every pair of `decodeQPairList (canonCode c)` has both endpoints in `[0, 1]`** — mirrors
`forall_lt_decodeQPairList_canonCode` (nondegeneracy), giving the companion boundedness fact. -/
theorem forall_bounds_decodeQPairList_canonCode (c : ℕ) :
    ∀ p ∈ decodeQPairList (canonCode c), 0 ≤ p.1 ∧ p.2 ≤ 1 := by
  unfold canonCode
  by_cases hz : canonListCode c = 0
  · have hzero : isZero (canonListCode c) = 1 := by rw [hz]; exact (isZero_eq_one_iff 0).mpr rfl
    rw [hzero, selectFn_one]
    intro p hp
    rw [decodeQPairList_masterCode, List.mem_singleton] at hp
    rw [hp]; norm_num
  · have hzero : isZero (canonListCode c) = 0 := by
      by_contra hcontra
      have h1 := isZero_le_one (canonListCode c)
      exact hz ((isZero_eq_one_iff _).mp (by omega))
    rw [hzero, selectFn_zero]
    intro p hp
    obtain ⟨p0, -, -, rfl⟩ := (mem_decodeQPairList_canonListCode c p).mp hp
    exact ⟨le_sup_right, inf_le_right⟩

end DomainTheory.NeighbourhoodSystems
