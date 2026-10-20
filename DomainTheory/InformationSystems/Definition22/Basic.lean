/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.Definition22.EntSet

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
