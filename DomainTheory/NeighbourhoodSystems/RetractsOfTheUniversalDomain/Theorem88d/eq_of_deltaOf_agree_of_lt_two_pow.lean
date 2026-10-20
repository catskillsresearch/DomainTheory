module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

























































/-- **Uniqueness of a bit-source below `2ⁿ`**: two bit-sources agreeing on every bit below `n` and
both `< 2ⁿ` are equal (every bit at or above `n` is forced `false` by the bound, so agreement below
`n` becomes agreement everywhere, and `Nat.eq_of_testBit_eq` finishes). -/
theorem eq_of_deltaOf_agree_of_lt_two_pow {n i j : ℕ} (hi : i < 2 ^ n) (hj : j < 2 ^ n)
    (hagree : ∀ l < n, deltaOf i l = deltaOf j l) : i = j := by
  apply Nat.eq_of_testBit_eq
  intro l
  rw [← deltaOf_eq_testBit, ← deltaOf_eq_testBit]
  rcases Nat.lt_or_ge l n with hl | hl
  · exact hagree l hl
  · have hile : 2 ^ n ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_lt_two_pow (hi.trans_le hile),
      Nat.testBit_lt_two_pow (hj.trans_le hile)]

end DomainTheory.NeighbourhoodSystems
