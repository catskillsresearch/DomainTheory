/-ai
This file gathers and re-exports Proposition 2.3 as the setting for Scott's Factoid 3.2, that every element contains the least informative token, because that proposition is true of every element.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

/-!
# Factoid 3.2 — every element contains Δ

**Factoid 3.2 (inventory).** Scott remarks after Def 3.1 that every element contains `Δ`,
because the least informative proposition is true of all elements.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)
end InfoSys
end DomainTheory.InformationSystems
