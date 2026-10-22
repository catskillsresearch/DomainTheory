/-ai
This file gathers and re-exports the definitions of a projection, a finitary retraction, and a finitary projection on an approximable self-map of a neighbourhood system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition82
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.IsFinitary
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83.FinitaryProjection

@[expose] public section

/-!
# Lecture VIII — Definition 8.3 (Scott 1981, PRG-19): projections and finitary retractions

**Definition 8.3.** A retraction `a : E → E` is called a *projection* provided `a ⊑ 1_E`; it is
*finitary* iff its fixed-point set is isomorphic to a domain.

Scott's remark right before the definition already shows every retraction of Proposition 8.2's
form is a projection: unwinding `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` gives `X ⊆ Z` immediately, i.e.
`a ⊑ I_E`. And Proposition 8.2's other half — `|D| ≅ Fix(a)` — says exactly that these retractions
are *finitary*, with `D` itself as the witnessing domain. So every `retractionOfSubsystem h` is a
finitary projection (`isProjection_retractionOfSubsystem`, `isFinitary_retractionOfSubsystem`).
Scott's remark that the converse fails ("not every retraction... even this condition is not
sufficient") is the content of Theorem 8.5, formalized separately.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}


namespace Subsystem

variable {h : D ◁ E}
end Subsystem
end DomainTheory.NeighbourhoodSystems
