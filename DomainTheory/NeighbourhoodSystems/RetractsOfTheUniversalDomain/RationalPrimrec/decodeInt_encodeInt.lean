/-ai
Decoding the encoding of an integer returns that integer.

Unfolding the two maps and cancelling the pairing, the sign of the integer splits the argument. If the integer is nonnegative, its truncation is itself and the truncation of its negation is zero. If it is negative, its truncation is zero and the truncation of its negation is the negation. In each case the difference of those truncations is the integer.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.decodeInt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.encodeInt

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

@[simp] theorem decodeInt_encodeInt (z : ℤ) : decodeInt (encodeInt z) = z := by
  unfold decodeInt encodeInt
  rw [unpair_pair]
  by_cases h : 0 ≤ z
  · have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
    have hnz : ((-z).toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show -z ≤ 0 by omega); simp [this]
    rw [hz, hnz]; ring
  · have h' : z < 0 := by omega
    have hz : (z.toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show z ≤ 0 from h'.le); simp [this]
    have hnz : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    rw [hz, hnz]; ring

end DomainTheory.NeighbourhoodSystems
