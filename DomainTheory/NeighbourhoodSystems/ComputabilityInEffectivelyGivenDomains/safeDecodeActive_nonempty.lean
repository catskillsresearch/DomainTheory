module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.safeDecodeActive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem safeDecodeActive_nonempty (n : ℕ) : (denote (safeDecodeActive n)).Nonempty := by
  unfold safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => exact Set.univ_nonempty
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hb]; exact (decideNonemptyB_iff e).mp hb
    · simp [hb, denote_sigma]

end Exercise722

end DomainTheory.NeighbourhoodSystems
