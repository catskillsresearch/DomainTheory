module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem decodeRatPair_qpCombineBop (e1 e2 : ℕ) :
    decodeRatPair (qpCombineBop (Nat.pair e1 e2))
      = ((decodeRatPair e1).1 ⊔ (decodeRatPair e2).1, (decodeRatPair e1).2 ⊓ (decodeRatPair e2).2) := by
  unfold qpCombineBop decodeRatPair
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_ratMaxCode, decodeRat_ratMinCode]

end DomainTheory.NeighbourhoodSystems
