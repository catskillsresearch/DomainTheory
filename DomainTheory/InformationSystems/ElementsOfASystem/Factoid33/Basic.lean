/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
