/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Definition22
import DomainTheory.InformationSystems.Proposition23.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(i).** `∅ ⊢ {Δ}`. -/
theorem proposition_2_3_i : sys.EntSet ∅ ({sys.bot} : Finset α) := by
  intro X hX
  rw [Finset.mem_singleton] at hX
  subst hX
  exact sys.ent_bot sys.con_empty

end InfoSys
end DomainTheory.InformationSystems
