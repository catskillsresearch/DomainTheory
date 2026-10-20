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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.rawDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.maxDepthInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst31

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem foldr_max_le_of_forall {s : Multiset (RawLamToken α)} {b : ℕ}
    (h : ∀ t ∈ s, rawDepth t ≤ b) :
    Multiset.foldr (maxDepthInsert (α := α)) 0 s ≤ b := by
  revert h
  refine Multiset.induction_on s ?_ ?_
  · intro; exact Nat.zero_le _
  · intro a s ih h
    simp only [Multiset.foldr_cons, maxDepthInsert]
    exact Nat.max_le.2 ⟨h a (Multiset.mem_cons_self _ _),
      ih fun t ht => h t (Multiset.mem_cons_of_mem ht)⟩

end InfoSys

end DomainTheory.InformationSystems
