module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.presentedIntervals_map_qpClipGe
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.mem_decodeQPairList_clipGeListCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem presentedIntervals_decodeQPairList_clipGeListCode (m c : ℕ) :
    presentedIntervals (decodeQPairList (clipGeListCode m c)) =
      presentedIntervals (decodeQPairList c) ∩ Set.Ici (decodeRat m) := by
  rw [← presentedIntervals_map_qpClipGe]
  apply presentedIntervals_congr
  intro p
  rw [mem_decodeQPairList_clipGeListCode, List.mem_map]
  simp only [eq_comm]

end DomainTheory.NeighbourhoodSystems
