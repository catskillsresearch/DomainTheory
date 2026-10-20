/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Factoid36
public import DomainTheory.InformationSystems.Factoid44
public import DomainTheory.InformationSystems.Factoid45.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `⊥ = ∅̄`. -/
theorem botElement_eq_closure_empty :
    sys.botElement = sys.closure (∅ : Finset α) sys.con_empty := by
  refine le_antisymm ?_ ?_
  · intro a ha
    -- ha : Ent {bot} a; show Ent ∅ a
    exact sys.ent_trans sys.con_empty (sys.con_sing sys.bot)
      (fun y hy => by
        have : y = sys.bot := Finset.mem_singleton.mp hy
        subst this
        exact sys.ent_bot sys.con_empty)
      ha
  · intro a ha
    -- ha : Ent ∅ a; show Ent {bot} a
    exact sys.ent_trans (sys.con_sing sys.bot) sys.con_empty
      (fun _ hy => False.elim (Finset.notMem_empty _ hy)) ha

end InfoSys
end DomainTheory.InformationSystems
