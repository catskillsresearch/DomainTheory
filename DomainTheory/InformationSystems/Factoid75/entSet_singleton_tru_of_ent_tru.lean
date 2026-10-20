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


























open ApproximableMap













theorem entSet_singleton_tru_of_ent_tru {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .tru) :
    boolSystem.EntSet ({BoolToken.tru} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have htru : boolSat p .tru := hAll p hp
  cases p with
  | undef => simp only [boolSat] at htru
  | isFalse => simp only [boolSat] at htru
  | isTrue =>
    have hsat : boolSat .isTrue t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat_bot _⟩
    | tru =>
      exact ⟨⟨.isTrue, fun s hs => by
          have : s = .tru := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .tru (Finset.mem_singleton_self _)⟩
    | fls => exact False.elim hsat

end InfoSys
end DomainTheory.InformationSystems
