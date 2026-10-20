module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableSplit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableDiff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.IsComputableUnion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx0_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateIdx1_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateJunk_packState2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateRemC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.stateInnerC_packStateC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair_fst_eq_testBit
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.deltaPair_snd_eq_testBit

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

/-- **Distinctness of bounded bit-sources**: two bit-sources both `< 4 ^ n` and unequal must
disagree (via `deltaPair`) at some position strictly below `n`. Unlike `Theorem88d.lean`'s
`eq_of_deltaOf_agree_of_lt_two_pow` (which this directly mirrors), agreement of `deltaPair k`/
`deltaPair k'` on `[0, n)` means agreement of `k.testBit`/`k'.testBit` on *every* bit `< 2 * n` (both
the `2 * i` and `2 * i + 1` readings) — covering all of `testBit`'s bits below the bound `4 ^ n =
2 ^ (2 * n)`, so `Nat.eq_of_testBit_eq` still finishes in one step once every bit position is routed
through `deltaPair_fst_eq_testBit`/`deltaPair_snd_eq_testBit`. -/
theorem eq_of_deltaPair_agree_of_lt_four_pow {n k k' : ℕ} (hk : k < 4 ^ n) (hk' : k' < 4 ^ n)
    (hagree : ∀ i < n, deltaPair k i = deltaPair k' i) : k = k' := by
  apply Nat.eq_of_testBit_eq
  intro l
  rcases Nat.lt_or_ge l (2 * n) with hl | hl
  · rcases Nat.mod_two_eq_zero_or_one l with hmod | hmod
    · have hl2 : l = 2 * (l / 2) := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.fst (hagree (l / 2) hi)
      rw [deltaPair_fst_eq_testBit, deltaPair_fst_eq_testBit] at heq
      rwa [hl2]
    · have hl2 : l = 2 * (l / 2) + 1 := by omega
      have hi : l / 2 < n := by omega
      have heq := congrArg Prod.snd (hagree (l / 2) hi)
      rw [deltaPair_snd_eq_testBit, deltaPair_snd_eq_testBit] at heq
      rwa [hl2]
  · have h4n : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    have hile : (2 : ℕ) ^ (2 * n) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
    rw [Nat.testBit_lt_two_pow ((h4n ▸ hk).trans_le hile),
      Nat.testBit_lt_two_pow ((h4n ▸ hk').trans_le hile)]

end DomainTheory.NeighbourhoodSystems
