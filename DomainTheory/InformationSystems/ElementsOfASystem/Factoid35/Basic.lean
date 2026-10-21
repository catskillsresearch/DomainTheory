/-ai
This file gathers and re-exports Proposition 2.3 and the entailment closure as the setting for Scott's Factoid 3.5. For a consistent finite set, the set of tokens it entails is an element of the domain, called a finite element.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.closure

@[expose] public section

/-!
# Factoid 3.5 — finite elements as entailment closures

**Factoid 3.5 (inventory).** For `u ∈ Con`, the closure
`ū = {X ∣ u ⊢ X}` is an element of `|A|` (a *finite element*).
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
