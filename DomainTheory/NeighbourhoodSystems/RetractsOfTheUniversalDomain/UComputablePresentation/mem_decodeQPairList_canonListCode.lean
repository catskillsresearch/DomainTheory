module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.qpClip
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.canonListCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation.mem_decodeQPairList_canonFilterStep

@[expose] public section

set_option linter.unusedSectionVars false

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
