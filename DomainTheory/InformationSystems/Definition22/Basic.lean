/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.InfoSys

/-!
# Definition 2.2 — set-level entailment

**Scott 1982, Definition 2.2.** For `u, v ∈ Con` we write `u ⊢ v` to mean that
`u ⊢ X` for all `X ∈ v`.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)

/-- **Definition 2.2 (Scott 1982).** Set-level entailment: `EntSet u v` means
`u ⊢ X` for every `X ∈ v`. -/
def EntSet (u v : Finset α) : Prop := ∀ X ∈ v, sys.Ent u X
end InfoSys
end DomainTheory.InformationSystems
