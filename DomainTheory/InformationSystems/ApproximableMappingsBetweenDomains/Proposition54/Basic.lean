/-ai
This module gathers and re-exports approximable mappings and the identity approximable mapping, as the setting for Proposition 5.4 of Scott 1982, which identifies the identity relation with entailment and shows that the identity acts as the identity on elements.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54.idMap

@[expose] public section

/-!
# Proposition 5.4 — the identity approximable mapping

**Scott 1982, Proposition 5.4.** `u I_A v ↔ u ⊢_A v`, and `I_A(x) = x`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
