/-ai
An approximable self-map is a projection when it is a retraction and it lies under the identity map of its neighbourhood system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}

/-- **Definition 8.3, first clause (Scott 1981, PRG-19).** A retraction `a : E → E` is a
*projection* provided `a ⊑ I_E`. (We do not separately require `Retraction a` in the
definition, matching Scott's usage where "projection" is applied to a retraction already in
hand; the conjunction is spelled out where needed, e.g. `FinitaryProjection`.) -/
def IsProjection (a : ApproximableMap E E) : Prop := Retraction a ∧ a ≤ idMap E

end DomainTheory.NeighbourhoodSystems
