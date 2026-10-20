/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Multiset.MapFold
import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid25
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid75.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap













theorem entSet_singleton_fls_of_ent_fls {u : Finset BoolToken}
    (_hu : u ∈ boolSystem.Con) (h : boolSystem.Ent u .fls) :
    boolSystem.EntSet ({BoolToken.fls} : Finset BoolToken) u := by
  intro t ht
  obtain ⟨⟨p, hp⟩, hAll⟩ := h
  have hfls : boolSat p .fls := hAll p hp
  cases p with
  | undef => simp only [boolSat] at hfls
  | isTrue => simp only [boolSat] at hfls
  | isFalse =>
    have hsat : boolSat .isFalse t := hp t ht
    cases t with
    | bot =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun _ _ => boolSat_bot _⟩
    | fls =>
      exact ⟨⟨.isFalse, fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial⟩, fun q hq => hq .fls (Finset.mem_singleton_self _)⟩
    | tru => exact False.elim hsat

end InfoSys
end DomainTheory.InformationSystems
