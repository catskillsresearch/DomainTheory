/-ai
The universal neighbourhood of the intersection code of two indices is either the master neighbourhood or the intersection of the two universal neighbourhoods.

That neighbourhood is the set of intervals presented by the canonical list of the decoded pair list, and the intervals presented by the decoded combined code are the intersection of the two universal neighbourhoods. If the filter of clipped positive pairs is empty, the canonical list is the singleton of the zero-one interval, which presents the master neighbourhood. If that filter is a nonempty list, the canonical list equals the filter, dropping the positivity filter and the clipping map leaves the presented intervals unchanged, and the subset component of the membership of the first universal neighbourhood cancels the remaining intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_finGenSys
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_nbhdGen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.mem_SubD
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.SubD_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section UniversalSubsystem

/-- **`Uinter`'s unconditional dichotomy.** Unlike a generic `ComputablePresentation.inter` (whose
behaviour off the consistent domain is unspecified "junk"), `𝒰`'s canonicalizing `Uinter` always
produces *either* the true intersection *or* falls back to `U.master` — `canonList`'s documented
"fall back to `(0,1)` if nothing survives" behaviour, holding **unconditionally** (no consistency
hypothesis needed). This is the key fact an abstract `ComputablePresentation` cannot supply. -/
theorem UX_Uinter_dichotomy (n m : ℕ) :
    UX (Uinter n m) = U.master ∨ UX (Uinter n m) = UX n ∩ UX m := by
  have hUXeq : UX (Uinter n m) = presentedIntervals (canonList (decodeQPairList (Uinter n m))) :=
    UX_eq (Uinter n m)
  have hL : presentedIntervals (decodeQPairList (Uinter n m)) = UX n ∩ UX m := by
    show presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))
        = UX n ∩ UX m
    rw [presentedIntervals_decodeQPairList_combineCode]
    rfl
  rcases hfilt : ((decodeQPairList (Uinter n m)).map qpClip).filter
      (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · left
    rw [hUXeq, canonList_eq_of_filter_eq_nil hfilt, presentedIntervals_singleton_zero_one]
  · right
    rw [hUXeq, canonList_eq_of_filter_eq_cons hfilt, ← hfilt, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, hL]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact Set.inter_eq_left.mpr (Set.inter_subset_left.trans hsubn)

end UniversalSubsystem

end DomainTheory.NeighbourhoodSystems
