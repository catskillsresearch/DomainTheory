/-ai
If two masks are strictly below two raised to two to the k and present the same level
set at level k, then the masks are equal.

It is enough that they have the same test bits. If the bit index is below two to the k,
extensionality of the level sets, the membership law, and the fact that the remainder of
the index by two to the k is the index itself reduce the two test bits to one Boolean,
and the four Boolean cases agree. If the index is at least two to the k, two to the
power two to the k is at most two to that index, so both masks lie strictly below two to
the index and both test bits are false.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem levelSet_inj_of_lt {k a b : ℕ} (ha : a < 2 ^ (2 ^ k)) (hb : b < 2 ^ (2 ^ k))
    (h : levelSet k a = levelSet k b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro ℓ
  by_cases hℓ : ℓ < 2 ^ k
  · have hiff := Set.ext_iff.mp h ℓ
    simp only [mem_levelSet, Nat.mod_eq_of_lt hℓ] at hiff
    cases ha' : a.testBit ℓ <;> cases hb' : b.testBit ℓ <;> simp_all
  · have hpow : (2:ℕ) ^ (2 ^ k) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hℓ)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

end DomainTheory.NeighbourhoodSystems
