module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.approxUnion

@[expose] public section

/-!
# Factoid 3.6 — every element is the directed union of its finite approximations

**Factoid 3.6 (Scott §3 / inventory).** For every element `x ∈ |A|`,
`x` equals the union of all `ū` with `u ∈ Con` and `u ⊆ x`.
Intuitively: every element is the limit of its finite approximations. The union is directed.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
