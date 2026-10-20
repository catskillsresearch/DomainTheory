/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
