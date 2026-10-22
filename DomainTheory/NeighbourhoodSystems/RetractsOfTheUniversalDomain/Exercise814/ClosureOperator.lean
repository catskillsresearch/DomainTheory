/-ai
A closure operator on a neighbourhood system is a retraction of the system into itself that lies above the identity map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Exercise 8.14 (Scott 1981, PRG-19), the definition.** A retraction `a : E → E` is a
*closure operator* iff `I_E ⊑ a`, i.e. `a` is inflationary. -/
class ClosureOperator (a : ApproximableMap E E) : Prop where
  out : Retraction a ∧ idMap E ≤ a

end DomainTheory.NeighbourhoodSystems
