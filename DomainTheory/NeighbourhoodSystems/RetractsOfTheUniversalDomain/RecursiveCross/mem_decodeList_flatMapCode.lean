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
