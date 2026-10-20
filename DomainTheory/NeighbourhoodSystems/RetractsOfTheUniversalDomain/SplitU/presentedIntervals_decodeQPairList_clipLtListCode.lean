module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_map_qpClipLt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.mem_decodeQPairList_clipLtListCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem










theorem presentedIntervals_decodeQPairList_clipLtListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipLtListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Iio (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipLt]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipLtListCode, List.mem_map]
  simp only [eq_comm]

end DomainTheory.NeighbourhoodSystems
