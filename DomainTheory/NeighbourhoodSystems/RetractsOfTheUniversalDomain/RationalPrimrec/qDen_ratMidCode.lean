/-ai
The denominator of the midpoint of two rational codes is twice the product of their denominators.

Each denominator is positive, so twice their product is positive and hence at least one. After the midpoint is unfolded and the pairing is cancelled, the stored second component is that product minus one, and adding one cancels the subtraction. Reordering the factors gives the stated product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec.qDen_pos

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem qDen_ratMidCode (c1 c2 : ℕ) : qDen (ratMidCode (Nat.pair c1 c2)) = qDen c1 * qDen c2 * 2 := by
  have h1 : 1 ≤ 2 * qDen c1 * qDen c2 := by
    have hd1 := qDen_pos c1
    have hd2 := qDen_pos c2
    have : 0 < 2 * qDen c1 * qDen c2 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hd2
    omega
  show (ratMidCode (Nat.pair c1 c2)).unpair.2 + 1 = qDen c1 * qDen c2 * 2
  simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [Nat.sub_add_cancel h1]; ring

end DomainTheory.NeighbourhoodSystems
