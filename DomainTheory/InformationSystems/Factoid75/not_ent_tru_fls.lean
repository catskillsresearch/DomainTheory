/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Multiset.MapFold
import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid25
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid75.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap












theorem not_ent_tru_fls : ¬ boolSystem.Ent {BoolToken.tru} BoolToken.fls := by
  intro ⟨⟨p, hp⟩, hAll⟩
  have htru : boolSat p .tru := hp .tru (Finset.mem_singleton_self _)
  have hfls : boolSat p .fls := hAll p hp
  cases p <;> simp only [boolSat] at htru hfls

end InfoSys
end DomainTheory.InformationSystems
