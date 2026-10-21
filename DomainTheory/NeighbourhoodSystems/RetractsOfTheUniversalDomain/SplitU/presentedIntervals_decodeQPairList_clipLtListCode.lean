/-ai
The intervals presented by the decoded downward list clip are the intervals presented by the source list, cut to the open ray below the decoded midpoint.

Rewrite by the rational downward-clip lemma and compare presented intervals. Membership of a pair in the clipped decoding is membership of its preimage under the clip in the source list.
ai-/
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
