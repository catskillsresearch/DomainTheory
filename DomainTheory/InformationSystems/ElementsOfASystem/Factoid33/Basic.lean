module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.botElement

@[expose] public section

/-!
# Factoid 3.3 — the bottom element ⊥

**Factoid 3.3 (inventory).** Scott defines
`⊥_A = {X ∈ D_A ∣ {Δ_A} ⊢_A X}` and notes it is the least element of `|A|`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
