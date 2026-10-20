/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Approximable
public import DomainTheory.InformationSystems.Proposition54.idMap

@[expose] public section

/-!
# Proposition 5.4 — the identity approximable mapping

**Scott 1982, Proposition 5.4.** `u I_A v ↔ u ⊢_A v`, and `I_A(x) = x`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

end InfoSys
end DomainTheory.InformationSystems
