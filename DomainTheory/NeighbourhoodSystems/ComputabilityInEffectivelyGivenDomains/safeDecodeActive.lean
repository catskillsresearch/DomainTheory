/-ai
The safe active decode of an index is the decoded expression when decoding succeeds and that expression denotes a nonempty set, and is sigma otherwise.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.decode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Canonical representative for `SsysX n` as a fragment expression (junk → `Σ`). -/
def safeDecodeActive (n : ℕ) : SExpr :=
  match SExpr.decode n with
  | none => .sigma
  | some e => if decideNonemptyB e then e else .sigma

end Exercise722

end DomainTheory.NeighbourhoodSystems
