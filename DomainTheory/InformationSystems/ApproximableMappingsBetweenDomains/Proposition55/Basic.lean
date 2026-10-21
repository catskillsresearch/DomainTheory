/-ai
This module gathers and re-exports the identity approximable mapping and composition of approximable mappings, as the setting for Proposition 5.5 of Scott 1982, which defines composition by an intermediate finite set and shows that a composite acts as composition on elements.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55.comp

@[expose] public section

/-!
# Proposition 5.5 — composition of approximable mappings

**Scott 1982, Proposition 5.5.** `u (g ∘ f) w ↔ ∃ v, u f v ∧ v g w`, and
`(g ∘ f)(x) = g(f(x))`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {A : InfoSys α} {B : InfoSys β} {C : InfoSys γ}

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
