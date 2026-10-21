/-ai
A code z lies in the decoded list of flatMapCode f x c if and only if z lies in the decoded list of f of the pair of x and some y from the decoded list of c.

Unfold flatMapCode, rewrite by the fold equation and the auxiliary membership lemma at the decoded list of c with empty accumulator, and drop the empty-list disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic

@[expose] public section


namespace Domain.Recursive


theorem mem_decodeList_flatMapCode {f : ℕ → ℕ} (x c z : ℕ) :
    z ∈ decodeList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, z ∈ decodeList (f (Nat.pair x y)) := by
  unfold flatMapCode
  rw [foldCode_eq', mem_decodeList_flatMapCode_aux f x (decodeList c) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

end Domain.Recursive
