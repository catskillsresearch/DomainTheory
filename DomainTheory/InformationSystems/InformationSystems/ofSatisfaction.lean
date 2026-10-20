/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.Sat
public import DomainTheory.InformationSystems.InformationSystems.sat_sing

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Generic information system from a satisfaction relation with a true `bot`
and inhabited singletons (Scott’s “obvious interpretation”).

`Ent` packages consistency of the left-hand set together with semantic entailment,
matching Scott’s typing of `⊢` as a relation on `Con × D` and making `ent_con`
hold (a purely vacuous `∀`-entailment from an inconsistent set would not). -/
def ofSatisfaction {τ : Type*} [DecidableEq τ] {Point : Type*}
    (Sat : Point → τ → Prop) (bot : τ)
    (sat_bot : ∀ p, Sat p bot)
    (sat_sing : ∀ t, ∃ p, Sat p t) : InfoSys τ where
  bot := bot
  Con := {u | ∃ p, ∀ t ∈ u, Sat p t}
  Ent u X := (∃ p, ∀ t ∈ u, Sat p t) ∧ ∀ p, (∀ t ∈ u, Sat p t) → Sat p X
  con_subset := by
    rintro u v ⟨p, hp⟩ hsub
    exact ⟨p, fun t ht => hp t (hsub ht)⟩
  con_sing := by
    intro a
    obtain ⟨p, hp⟩ := sat_sing a
    exact ⟨p, fun t ht => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hp⟩
  ent_con := by
    rintro u a ⟨⟨p, hp⟩, hEnt⟩
    exact ⟨p, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hEnt p hp
      · exact hp t ht'⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, fun p _ => sat_bot p⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, fun p hp => hp a ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, huEnt⟩
    refine ⟨hv, fun p hp => huEnt p ?_⟩
    intro y hy
    exact (hvu y hy).2 p hp

end Factoid25

end DomainTheory.InformationSystems
