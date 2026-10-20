/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Sum
import Mathlib.Data.Finset.Card
import DomainTheory.InformationSystems.Factoid82.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



theorem LamCon_singleton_atom (x : α) :
    LamCon A ({.atom x} : Finset (RawLamToken α)) := by
  refine ⟨0, ?_⟩
  change lamAtomFinset _ ∈ A.Con ∧ lamFunFinset _ = ∅
  constructor
  · have h : lamAtomFinset ({.atom x} : Finset (RawLamToken α)) = {x} := by
      ext y
      simp only [mem_lamAtomFinset, Finset.mem_singleton]
      exact ⟨RawLamToken.atom.inj, congrArg RawLamToken.atom⟩
    rw [h]; exact A.con_sing x
  · ext p
    constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)

end InfoSys
end DomainTheory.InformationSystems
