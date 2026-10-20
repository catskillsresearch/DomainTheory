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
import DomainTheory.InformationSystems.Factoid82.mem_lamForgetFinset


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



























theorem lamForgetFinset_insert (u : Finset (LamToken A)) (p : LamToken A) :
    lamForgetFinset A (insert p u) = insert p.val (lamForgetFinset A u) := by
  ext t
  constructor
  · intro ht
    rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_lamForgetFinset A).2 ⟨q, hq, rfl⟩)
  · intro ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact (mem_lamForgetFinset A).2 ⟨p, Finset.mem_insert_self p u, rfl⟩
    · rcases (mem_lamForgetFinset A).1 ht with ⟨q, hq, rfl⟩
      exact (mem_lamForgetFinset A).2 ⟨q, Finset.mem_insert_of_mem hq, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
