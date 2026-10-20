/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Factoid35
public import DomainTheory.InformationSystems.Factoid75.BoolToken
public import DomainTheory.InformationSystems.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.Factoid75.mem_toFunFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem toFunFinset_insert (w : Finset (StrictFunToken A B)) (p : StrictFunToken A B) :
    toFunFinset A B (insert p w) = insert p.val (toFunFinset A B w) := by
  ext q
  constructor
  · intro hq
    rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_toFunFinset A B).2 ⟨r, hr, rfl⟩)
  · intro hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (mem_toFunFinset A B).2 ⟨p, Finset.mem_insert_self _ _, rfl⟩
    · rcases (mem_toFunFinset A B).1 hq with ⟨r, hr, rfl⟩
      exact (mem_toFunFinset A B).2 ⟨r, Finset.mem_insert_of_mem hr, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
