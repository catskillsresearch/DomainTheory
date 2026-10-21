/-ai
The token type of the separated sum of token sets α and β, Scott's Definition 6.3(i) and (ii), is the inductive type with a left constructor from α, a right constructor from β, and a bottom constructor. Scott writes the left token as (X, Δ), the right token as (Δ, Y), and the bottom token as (Δ, Δ).
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Token type of the separated sum `A + B` (Scott 6.3(i)–(ii)).
`left X` is `(X, Δ)`, `right Y` is `(Δ, Y)`, and `bot` is `(Δ, Δ)`. -/
inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β

end InfoSys
end DomainTheory.InformationSystems
