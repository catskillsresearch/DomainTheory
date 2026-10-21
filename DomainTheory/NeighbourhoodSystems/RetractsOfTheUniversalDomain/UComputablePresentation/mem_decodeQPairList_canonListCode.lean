/-ai
A rational pair lies in the list decoded from a canonical list code if and only if it is the nondegenerate clip of some pair decoded from the original code. The canonical list code realizes the clip-and-filter pass.

Unfold the list code and rewrite membership through the flat map. A witness code has second component in the filter step, hence equal to the nondegenerate clip of its decoded pair, and that decoded pair lies in the original list. Conversely, a source pair is the decoding of some code in the original list, and that code's second component lies in the filter step.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonFilterStep

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`canonListCode` realizes the clip-and-filter pass at the set level.** -/
theorem mem_decodeQPairList_canonListCode (c : ℕ) (p : ℚ × ℚ) :
    p ∈ decodeQPairList (canonListCode c) ↔
      ∃ p0 ∈ decodeQPairList c, (qpClip p0).1 < (qpClip p0).2 ∧ p = qpClip p0 := by
  unfold canonListCode
  rw [mem_decodeQPairList_flatMapCode]
  constructor
  · rintro ⟨y, hy, hp⟩
    rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep] at hp
    exact ⟨decodeRatPair y, (mem_decodeQPairList c (decodeRatPair y)).mpr ⟨y, hy, rfl⟩, hp⟩
  · rintro ⟨p0, hp0, hcond, hp⟩
    obtain ⟨y, hy, rfl⟩ := (mem_decodeQPairList c p0).mp hp0
    exact ⟨y, hy, by rw [unpair_pair_snd, mem_decodeQPairList_canonFilterStep]; exact ⟨hcond, hp⟩⟩

end DomainTheory.NeighbourhoodSystems
