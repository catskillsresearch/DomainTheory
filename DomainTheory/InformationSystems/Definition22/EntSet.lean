/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys

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
