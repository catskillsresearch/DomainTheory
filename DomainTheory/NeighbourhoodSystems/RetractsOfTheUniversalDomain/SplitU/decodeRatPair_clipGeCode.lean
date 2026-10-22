module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem decodeRatPair_clipGeCode (m e : ℕ) :
    decodeRatPair (clipGeCode (Nat.pair m e)) = qpClipGe (decodeRat m) (decodeRatPair e) := by
  unfold clipGeCode decodeRatPair qpClipGe
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMaxCode]

end DomainTheory.NeighbourhoodSystems
