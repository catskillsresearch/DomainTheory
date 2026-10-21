/-ai
A rational pair lies in the decoding of a combination code if and only if it is the join of the left endpoints and the meet of the right endpoints of a pair from each decoded list.

Unfold the decoding and the combination code. A preimage in the cross combination supplies two codes, one from each list, and decoding the combination operation yields the join-meet pair. Conversely, mapped membership supplies the two codes, and cross-combination membership together with the decoding of the operation restores the preimage.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.decodeRatPair_qpCombineBop

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive


theorem mem_decodeQPairList_combineCode (c1 c2 : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (combineCode c1 c2) ↔
      ∃ p1 ∈ decodeQPairList c1, ∃ p2 ∈ decodeQPairList c2, p = (p1.1 ⊔ p2.1, p1.2 ⊓ p2.2) := by
  unfold decodeQPairList combineCode
  rw [List.mem_map]
  constructor
  · rintro ⟨z, hz, hpz⟩
    rw [mem_decodeList_crossCombine] at hz
    obtain ⟨e1, he1, e2, he2, hze⟩ := hz
    refine ⟨decodeRatPair e1, List.mem_map_of_mem he1, decodeRatPair e2, List.mem_map_of_mem he2, ?_⟩
    rw [← hpz, hze, decodeRatPair_qpCombineBop]
  · rintro ⟨p1, hp1, p2, hp2, hp⟩
    obtain ⟨e1, he1, he1'⟩ := List.mem_map.mp hp1
    obtain ⟨e2, he2, he2'⟩ := List.mem_map.mp hp2
    refine ⟨qpCombineBop (Nat.pair e1 e2),
      (mem_decodeList_crossCombine (bop := qpCombineBop) c1 c2 _).mpr ⟨e1, he1, e2, he2, rfl⟩, ?_⟩
    rw [decodeRatPair_qpCombineBop, he1', he2', hp]

end DomainTheory.NeighbourhoodSystems
