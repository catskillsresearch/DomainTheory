/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

/-!
# Factoid 3.2 — every element contains Δ

**Factoid 3.2 (inventory).** Scott remarks after Def 3.1 that every element contains `Δ`,
because the least informative proposition is true of all elements.
-/

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)
end InfoSys
end DomainTheory.InformationSystems
