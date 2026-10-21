/-ai
The activity bit of an index is false when decoding fails, and otherwise is the decision that the decoded expression denotes a nonempty set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Inactive index: decode fails or denotes the empty language (mapped to `Σ` in `SsysX`). -/
def ssysActive (n : ℕ) : Bool :=
  match SExpr.decode n with
  | none => false
  | some e => decideNonemptyB e

end Exercise722

end DomainTheory.NeighbourhoodSystems
