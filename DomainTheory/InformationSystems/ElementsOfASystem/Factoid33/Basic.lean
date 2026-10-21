/-ai
This file gathers and re-exports Factoid 3.2 and the bottom element as the setting for Scott's Factoid 3.3. The bottom element is the set of tokens entailed by the singleton of the least informative token, and it is the least element of the domain.
ai-/

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
