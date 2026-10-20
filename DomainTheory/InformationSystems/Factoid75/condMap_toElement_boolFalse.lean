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
import DomainTheory.InformationSystems.Factoid75.not_ent_fls_tru
import DomainTheory.InformationSystems.Factoid75.not_emptyEntails_singleton_fls


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)


























open ApproximableMap












theorem condMap_toElement_boolFalse (x y : A.Element) :
    (condMap A x y).toElement boolFalse = y := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨huC, _, hE, _, hf⟩⟩
    rcases boolCon_trichotomy huC with hEmp | hTru | hFls
    · exact (botElement_le A y)
        (emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _)))
    · exfalso
      obtain ⟨⟨_, _⟩, hAll⟩ := hTru
      have : boolSat .isFalse .tru := hAll .isFalse fun t ht' =>
        (hu (Finset.mem_coe.2 ht')).2 .isFalse fun s hs => by
          have : s = .fls := Finset.mem_singleton.mp hs
          subst this; trivial
      simp only [boolSat] at this
    · exact hf hFls (Finset.mem_coe.2 (Finset.mem_singleton_self _))
  · intro Z hZ
    refine ⟨{BoolToken.fls}, ?_, boolSystem.con_sing _, A.con_sing _, ?_, ?_, ?_⟩
    · intro t ht
      have : t = .fls := Finset.mem_singleton.mp (Finset.mem_coe.1 ht)
      subst this
      exact (boolSystem.subset_closure (boolSystem.con_sing _))
        (Finset.mem_coe.2 (Finset.mem_singleton_self _))
    · exact fun hEmp => False.elim (not_emptyEntails_singleton_fls hEmp)
    · exact fun hTru => False.elim (not_ent_fls_tru hTru)
    · intro _ z hz
      have : z = Z := Finset.mem_singleton.mp (Finset.mem_coe.1 hz)
      subst this; exact hZ

end InfoSys
end DomainTheory.InformationSystems
