/-ai
A rational pair lies in the decoded list of the downward list clip if and only if it is the downward clip, at the decoded midpoint, of some pair in the decoded source list.

Unfold the list clip and rewrite by flat-map membership. From a source code, singleton decoding and the clip-decoding lemma recover the clipped pair, which lies in the source list. Conversely, a source pair is the decoding of some list element, and the same two lemmas put the clipped pair back into the singleton decoding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.decodeRatPair_clipLtCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.decodeQPairList_singletonCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem mem_decodeQPairList_clipLtListCode (m c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (clipLtListCode m c) ↔
      ∃ p0 ∈ decodeQPairList c, p = qpClipLt (decodeRat m) p0 := by
  unfold clipLtListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by
      rw [decodeQPairList_singletonCode, List.mem_singleton, decodeRatPair_clipLtCode]; exact hp⟩

end DomainTheory.NeighbourhoodSystems
