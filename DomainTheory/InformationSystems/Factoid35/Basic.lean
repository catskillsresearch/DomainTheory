/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Proposition23

@[expose] public section

/-!
# Factoid 3.5 — finite elements as entailment closures

**Factoid 3.5 (inventory).** For `u ∈ Con`, the closure
`ū = {X ∣ u ⊢ X}` is an element of `|A|` (a *finite element*).
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.5.** Entailment closure of a consistent set. -/
def closure (u : Finset α) (hu : u ∈ sys.Con) : sys.Element where
  carrier := {X | sys.Ent u X}
  consistent := by
    intro Y hY
    have hEnt : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
    exact sys.con_subset (proposition_2_3_ii sys hu hEnt) (subset_funion_right _ _)
  closed := by
    intro Y a hY hEnt
    have hYcon : Y ∈ sys.Con := by
      have hEntY : sys.EntSet u Y := fun X hX => hY (Finset.mem_coe.2 hX)
      exact sys.con_subset (proposition_2_3_ii sys hu hEntY) (subset_funion_right _ _)
    exact sys.ent_trans hu hYcon (fun y hy => hY (Finset.mem_coe.2 hy)) hEnt
end InfoSys
end DomainTheory.InformationSystems
