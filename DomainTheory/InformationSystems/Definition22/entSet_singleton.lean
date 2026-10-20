/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.InfoSys
import DomainTheory.InformationSystems.Definition22.Basic


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)


theorem entSet_singleton {u : Finset α} {X : α} :
    sys.EntSet u {X} ↔ sys.Ent u X := by
  constructor
  · intro h
    exact h X (Finset.mem_singleton_self X)
  · intro h Y hY
    rw [Finset.mem_singleton] at hY
    subst hY
    exact h

end InfoSys
end DomainTheory.InformationSystems
