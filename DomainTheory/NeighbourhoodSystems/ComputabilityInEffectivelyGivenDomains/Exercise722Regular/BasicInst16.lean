/-ai
The instance decidableMemDenote decides whether a word belongs to the language of an expression. It decides the Boolean matcher and transports the answer along the equivalence between matcher acceptance and denotation membership.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722
public import Mathlib.Logic.Encodable.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.SExpr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.BasicInst7
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_sigma
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_single
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.denote_cap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.matchesB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.matchesB_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- **Membership in a regular event is decidable** (choice-free), via the matcher. -/
instance decidableMemDenote (e : SExpr) : DecidablePred (· ∈ denote e) :=
  fun w => decidable_of_iff (matchesB e w = true) (matchesB_iff e w)

end Exercise722

end DomainTheory.NeighbourhoodSystems
