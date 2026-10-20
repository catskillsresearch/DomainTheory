/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamOutputUnion_singleton (p : List (RawLamToken α) × List (RawLamToken α)) :
    lamOutputUnion ({p} : Finset (List (RawLamToken α) × List (RawLamToken α))) =
      listToFinset p.2 := by
  ext t
  change t ∈ listToFinset p.2 ∪' ∅ ↔ t ∈ listToFinset p.2
  simp only [mem_funion, Finset.notMem_empty, or_false]

end InfoSys

end DomainTheory.InformationSystems
