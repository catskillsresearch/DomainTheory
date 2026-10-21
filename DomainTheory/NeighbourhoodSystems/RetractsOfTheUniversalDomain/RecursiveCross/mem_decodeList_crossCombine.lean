/-ai
A code z lies in the decoded list of crossCombine bop c1 c2 if and only if z equals bop of the pair of some x from the decoded list of c1 and some y from the decoded list of c2.

Unfold crossCombine, rewrite by the fold equation and the auxiliary membership lemma at the decoded list of c1 with empty accumulator, and drop the empty-list disjunct.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic

@[expose] public section


namespace Domain.Recursive


theorem mem_decodeList_crossCombine {bop : ℕ → ℕ} (c1 c2 z : ℕ) :
    z ∈ decodeList (crossCombine bop c1 c2) ↔
      ∃ x ∈ decodeList c1, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossCombine
  rw [foldCode_eq', mem_decodeList_crossCombine_aux bop c2 (decodeList c1) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

end Domain.Recursive
