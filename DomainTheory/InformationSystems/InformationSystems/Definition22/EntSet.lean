/-ai
Set-level entailment holds of finite sets u and v when u entails every token that belongs to v.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- **Definition 2.2 (Scott 1982).** Set-level entailment: `EntSet u v` means
`u ⊢ X` for every `X ∈ v`. -/
def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X

end InfoSys

end DomainTheory.InformationSystems
