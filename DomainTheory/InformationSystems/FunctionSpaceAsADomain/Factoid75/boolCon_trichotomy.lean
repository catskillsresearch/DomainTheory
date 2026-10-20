/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat_bot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem boolCon_trichotomy {u : Finset BoolToken} (hu : u ∈ boolSystem.Con) :
    EmptyEntails boolSystem u ∨ boolSystem.Ent u .tru ∨ boolSystem.Ent u .fls := by
  obtain ⟨p, hp⟩ := hu
  cases p with
  | undef =>
    refine Or.inl fun t ht => ?_
    have hsat := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
        fun _ _ => boolSat_bot _⟩
    | tru => exact False.elim hsat
    | fls => exact False.elim hsat
  | isTrue =>
    if htru : BoolToken.tru ∈ u then
      exact Or.inr (Or.inl ⟨⟨.isTrue, hp⟩, fun q hq => hq _ htru⟩)
    else
      refine Or.inl fun t ht => ?_
      have hsat := hp t ht
      cases t with
      | bot =>
        exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
          fun _ _ => boolSat_bot _⟩
      | tru => exact False.elim (htru ht)
      | fls => exact False.elim hsat
  | isFalse =>
    if hfls : BoolToken.fls ∈ u then
      exact Or.inr (Or.inr ⟨⟨.isFalse, hp⟩, fun q hq => hq _ hfls⟩)
    else
      refine Or.inl fun t ht => ?_
      have hsat := hp t ht
      cases t with
      | bot =>
        exact ⟨⟨.undef, fun _ h => False.elim (Finset.notMem_empty _ h)⟩,
          fun _ _ => boolSat_bot _⟩
      | tru => exact False.elim hsat
      | fls => exact False.elim (hfls ht)

end InfoSys

end DomainTheory.InformationSystems
