/-ai
The comparison code of two rational codes equals one if and only if the first decoded rational is at most the second.

Unfolding the comparison code and cancelling the pairing, the zero test equals one exactly when the truncated difference vanishes, hence when the first cross-cleared sum is at most the second. The component form of decoding and the division form of the rational constructor rewrite the rational comparison as a comparison of quotients. Both denominators are positive, so that comparison is the inequality of the cross-cleared numerators. The two directions of the resulting arithmetic comparison follow by linear arithmetic.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen_pos

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


/-- **Correctness of `ratLeCode`**: it is `1` exactly when the decoded rationals compare `≤`. -/
theorem ratLeCode_eq_one_iff (c1 c2 : ℕ) :
    ratLeCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 ≤ decodeRat c2 := by
  unfold ratLeCode
  rw [unpair_pair_fst, unpair_pair_snd, isZero_eq_one_iff, Nat.sub_eq_zero_iff_le]
  rw [decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div,
    div_le_div_iff₀ (by exact_mod_cast qDen_pos c1) (by exact_mod_cast qDen_pos c2),
    ← Nat.cast_le (α := ℚ)]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

end DomainTheory.NeighbourhoodSystems
