/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.finsetMaxDepth_listToFinset_le

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem finsetMaxDepth_list_lt_funTok (u v : List (RawLamToken α)) :
    finsetMaxDepth (listToFinset u) < rawDepth (.funTok u v) := by
  have h1 := finsetMaxDepth_listToFinset_le u
  have h2 : List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u ≤
      Nat.max (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u)
        (List.foldl (fun d t => Nat.max d (rawDepth t)) 0 v) :=
    Nat.le_max_left _ _
  simp only [rawDepth]
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_add_of_pos_left (Nat.succ_pos 0))

end InfoSys

end DomainTheory.InformationSystems
