module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem decodeRatPair_clipLtCode (m e : ℕ) :
    decodeRatPair (clipLtCode (Nat.pair m e)) = qpClipLt (decodeRat m) (decodeRatPair e) := by
  unfold clipLtCode decodeRatPair qpClipLt
  simp only [unpair_pair_fst, unpair_pair_snd, decodeRat_ratMinCode]

end DomainTheory.NeighbourhoodSystems
