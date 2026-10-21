/-ai
The success bit returned by one meet step is at most one.

Each application of the one-test yields zero or one. If the accumulator test is zero, the product is zero and selection returns the failure code, whose first component is zero. If it is one, the same split on the consistency test returns either zero or one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_eq_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.isomorphic_DprimeU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8_a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.theorem_8_8
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable (cons : ℕ → ℕ)


theorem meetStep_ok_le_one (r i : ℕ) : (meetStep P cons r i).unpair.1 ≤ 1 := by
  have h1 := isOne_le_one r.unpair.1
  have h2 := isOne_le_one (cons (Nat.pair r.unpair.2 i))
  unfold meetStep
  rcases (show isOne r.unpair.1 = 0 ∨ isOne r.unpair.1 = 1 by omega) with h | h
  · rw [h, Nat.zero_mul, selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
  · rw [h, Nat.one_mul]
    rcases (show isOne (cons (Nat.pair r.unpair.2 i)) = 0 ∨
        isOne (cons (Nat.pair r.unpair.2 i)) = 1 by omega) with h' | h'
    · rw [h', selectFn_zero, unpair_pair_fst]; exact Nat.zero_le 1
    · rw [h', selectFn_one, unpair_pair_fst]

end DomainTheory.NeighbourhoodSystems
