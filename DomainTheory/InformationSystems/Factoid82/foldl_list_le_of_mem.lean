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
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.Factoid82.rawDepth
public import DomainTheory.InformationSystems.Factoid82.foldl_max_mono_init
public import DomainTheory.InformationSystems.Factoid82.foldl_max_ge_init

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem foldl_list_le_of_mem {t : RawLamToken α} {u : List (RawLamToken α)}
    (ht : t ∈ u) :
    rawDepth t ≤ List.foldl (fun d t => Nat.max d (rawDepth t)) 0 u := by
  induction u with
  | nil => cases ht
  | cons a as ih =>
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right 0 (rawDepth t))
        (foldl_max_ge_init as (Nat.max 0 (rawDepth t)))
    · exact Nat.le_trans (ih ht) (foldl_max_mono_init (Nat.zero_le _))

end InfoSys

end DomainTheory.InformationSystems
