module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX_default
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem SsysX_eq_denote_safe (n : ℕ) : SsysX n = denote (safeDecodeActive n) := by
  unfold SsysX safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => simp [denote_sigma, SsysX_default]
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hb]
    · simp [hb, denote_sigma, SsysX_default]

end Exercise722

end DomainTheory.NeighbourhoodSystems
