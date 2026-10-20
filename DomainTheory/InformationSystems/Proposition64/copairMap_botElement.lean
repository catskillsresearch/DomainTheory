/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid33
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition64.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}





theorem copairMap_botElement (f : ApproximableMap A C) (g : ApproximableMap B C) :
    (copairMap A B f g).toElement (sumSystem A B).botElement = C.botElement := by
  apply le_antisymm
  · intro Y ⟨u, hu, ⟨huCon, hs, hcop⟩⟩
    have onlyBot : ∀ p ∈ u, p = SumToken.bot (α := α) (β := β) := by
      intro p hp
      have hEnt : (sumSystem A B).Ent {sumBot} p := hu (Finset.mem_coe.2 hp)
      cases p with
      | bot => rfl
      | left x =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : lftFinset ({sumBot} : Finset (SumToken α β)) = ∅ := lftFinset_singleton_bot
          exact hne this)
      | right y =>
        exact False.elim (by
          have hne := hEnt.2.1
          have : rhtFinset ({sumBot} : Finset (SumToken α β)) = ∅ := rhtFinset_singleton_bot
          exact hne this)
    have hl : lftFinset u = ∅ := by
      ext x; constructor
      · intro hx; exact False.elim (nomatch onlyBot _ ((mem_lftFinset).1 hx))
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
    have hr : rhtFinset u = ∅ := by
      ext y; constructor
      · intro hy; exact False.elim (nomatch onlyBot _ ((mem_rhtFinset).1 hy))
      · intro hy; exact False.elim (Finset.notMem_empty y hy)
    rcases hcop with hE | ⟨hne, _⟩ | ⟨hne, _⟩
    · exact C.ent_trans (C.con_sing C.bot) C.con_empty
        (fun _ hz => False.elim (Finset.notMem_empty _ hz))
        (hE Y (Finset.mem_singleton_self _))
    · exact False.elim (hne hl)
    · exact False.elim (hne hr)
  · intro Y hY
    refine ⟨∅, fun _ hp => False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 hp)), ?_⟩
    refine ⟨SumCon_empty A B, C.con_sing Y, Or.inl ?_⟩
    intro Z hZ
    have : Z = Y := Finset.mem_singleton.mp hZ
    subst this
    exact C.ent_trans C.con_empty (C.con_sing C.bot)
      (fun _ hz => by
        have : _ = C.bot := Finset.mem_singleton.mp hz
        subst this
        exact C.ent_bot C.con_empty)
      hY

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
