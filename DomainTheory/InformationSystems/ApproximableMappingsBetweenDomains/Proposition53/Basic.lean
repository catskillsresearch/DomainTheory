/-ai
This module gathers and re-exports approximable mappings and their inclusion order, as the setting for Proposition 5.3 of Scott 1982. The proposition records the singleton reduction, the closure bridge between a relation and inclusion of images of closures, the pointwise order, and extensionality through elements, after the image of an element and its monotonicity.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Le

@[expose] public section

/-!
# Proposition 5.3 — images, order, and the closure bridge

**Scott 1982, Proposition 5.3.** Remaining clauses after Def 5.2 / `toElement`:
singleton reduction (Scott’s remark before Def 5.2); (v) the bridge
`u f v ↔ v̄ ⊆ f(ū)`; (iii) pointwise order; (ii) extensionality via elements.
(i) and (iv) are already `toElement` / `toElement_mono` in `Approximable.lean`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {A : InfoSys α} {B : InfoSys β}

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
