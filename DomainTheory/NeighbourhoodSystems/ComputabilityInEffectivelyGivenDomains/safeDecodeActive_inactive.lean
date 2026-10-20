module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysActive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem safeDecodeActive_inactive (n : ℕ) (h : ssysActive n = false) : safeDecodeActive n = .sigma := by
  dsimp only [ssysActive, safeDecodeActive] at h ⊢
  cases hdec : SExpr.decode n with
  | none => rfl
  | some e =>
    by_cases hb : decideNonemptyB e
    · exfalso
      simp [hdec, hb] at h
    · simp [hb]

end Exercise722

end DomainTheory.NeighbourhoodSystems
