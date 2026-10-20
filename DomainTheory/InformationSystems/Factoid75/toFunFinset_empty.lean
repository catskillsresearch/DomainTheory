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
public import DomainTheory.InformationSystems.Factoid75.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


















theorem toFunFinset_empty :
    toFunFinset A B (∅ : Finset (StrictFunToken A B)) = (∅ : Finset (FunToken A B)) := by
  ext p
  constructor
  · intro hp
    rcases (mem_toFunFinset A B).1 hp with ⟨_, hq, _⟩
    exact False.elim (Finset.notMem_empty _ hq)
  · intro hp
    exact False.elim (Finset.notMem_empty _ hp)

end InfoSys
end DomainTheory.InformationSystems
