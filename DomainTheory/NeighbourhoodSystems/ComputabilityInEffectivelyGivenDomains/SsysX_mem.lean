module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

theorem SsysX_mem (n : ℕ) : InS (SsysX n) := by
  unfold SsysX
  cases hdec : SExpr.decode n with
  | none => simp; exact InS.univ
  | some e =>
    by_cases h : decideNonemptyB e = true
    · simp [h]
      exact InS_denote_of_nonempty ((decideNonemptyB_iff e).1 h)
    · simp [h]
      exact InS.univ

end Exercise722

end DomainTheory.NeighbourhoodSystems
