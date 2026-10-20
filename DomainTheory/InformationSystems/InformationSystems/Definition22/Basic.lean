module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Definition22.EntSet

@[expose] public section

/-!
# Definition 2.2 — set-level entailment

**Scott 1982, Definition 2.2.** For `u, v ∈ Con` we write `u ⊢ v` to mean that
`u ⊢ X` for all `X ∈ v`.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
