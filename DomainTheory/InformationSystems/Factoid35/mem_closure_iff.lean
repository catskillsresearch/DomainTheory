/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Proposition23
import DomainTheory.InformationSystems.Factoid35.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem mem_closure_iff {u : Finset α} (hu : u ∈ sys.Con) {X : α} :
    X ∈ (sys.closure u hu).carrier ↔ sys.Ent u X := Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
