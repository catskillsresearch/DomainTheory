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
