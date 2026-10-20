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
