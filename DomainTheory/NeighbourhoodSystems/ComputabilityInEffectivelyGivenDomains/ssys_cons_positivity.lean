/-ai
Some neighbourhood of the system is contained in the intersection of the neighbourhoods at two indices if and only if that intersection is nonempty.

A contained neighbourhood is itself nonempty, so the intersection is nonempty. Conversely, a nonempty intersection of two neighbourhoods of the system belongs to the system by positivity, and surjectivity of the enumeration supplies an index whose neighbourhood is contained in the intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Ssys_isPositive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_surj

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem ssys_cons_positivity (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ (SsysX n ∩ SsysX m).Nonempty := by
  constructor
  · intro ⟨k, hk⟩
    exact Set.Nonempty.mono hk (InS.nonempty (SsysX_mem k))
  · intro hne
    have hIn : InS (SsysX n ∩ SsysX m) :=
      (Ssys_isPositive (Ssys_mem.mpr (SsysX_mem n)) (Ssys_mem.mpr (SsysX_mem m))).2 hne
    obtain ⟨k, hk⟩ := SsysX_surj hIn
    exact ⟨k, hk.subset⟩

end Exercise722

end DomainTheory.NeighbourhoodSystems
