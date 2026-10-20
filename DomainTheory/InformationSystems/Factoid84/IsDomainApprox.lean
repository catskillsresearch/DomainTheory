/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Factoid34
public import DomainTheory.InformationSystems.Factoid35

@[expose] public section

namespace DomainTheory.InformationSystems
namespace Factoid84

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

/-- Minimal entailment on `ℕ` with `0 = Δ`: `u ⊢ n` iff `n = 0` or `n ∈ u`. -/
def PEnt (u : Finset ℕ) (n : ℕ) : Prop :=
  n = 0 ∨ n ∈ u

/-- **Powerset information system.** Tokens `ℕ`, bot `0`, every finite set
consistent, minimal entailment. -/
def P : InfoSys ℕ where
  bot := 0
  Con := Set.univ
  Ent := PEnt
  con_subset := fun _ _ => trivial
  con_sing := fun _ => trivial
  ent_con := fun _ => trivial
  ent_bot := fun _ => Or.inl rfl
  ent_refl := fun _ ha => Or.inr ha
  ent_trans := by
    intro u v c _ _ hEnts hc
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · exact hEnts c hc

theorem P_AllConsistent : P.AllConsistent := fun _ => trivial

/-- Scott’s shorthand `\bar n = {n}` as a finite set of tokens. -/
def bar (n : ℕ) : Finset ℕ := {n}

/-- Finite element `\bar n` (entailment closure of `{n}`). -/
def barElement (n : ℕ) : P.Element :=
  P.closure (bar n) trivial

/-- Bottom element `⊥` of `|P|` (closure of `∅`). -/
def botElement : P.Element :=
  P.closure ∅ trivial

/-- Top element `⊤` of `|P|` (all tokens). -/
def topElement : P.Element :=
  P.topElement P_AllConsistent

/-- (1) `I_P ⊆ r` (reflexivity of the induced entailment). -/
def ReflApprox (r : ApproximableMap P P) : Prop :=
  ∀ {u v : Finset ℕ}, (idMap P).rel u v → r.rel u v

/-- (2) `r ∘ r = r` (transitivity / idempotence). -/
def IdemApprox (r : ApproximableMap P P) : Prop :=
  ApproximableMap.comp r r = r

/-- (3) `\bar 0 ⊆ r(⊥)` — `0` plays the rôle of `Δ`. -/
def BotApprox (r : ApproximableMap P P) : Prop :=
  (barElement 0).carrier ⊆ (r.toElement botElement).carrier

/-- (4) `⊤ = r(\bar 1)` — `1` plays the rôle of the rogue `∇`. -/
def RogueApprox (r : ApproximableMap P P) : Prop :=
  r.toElement (barElement 1) = topElement

/-- (5) `\bar 1 ⊈ r(\bar 0)` — `1` is excluded as inconsistent at the bottom. -/
def ConsistentApprox (r : ApproximableMap P P) : Prop :=
  ¬ ((barElement 1).carrier ⊆ (r.toElement (barElement 0)).carrier)

/-- Scott (1)–(5): approximable maps that present entailment relations / domains. -/
structure IsDomainApprox (r : ApproximableMap P P) : Prop where
  refl : ReflApprox r
  idem : IdemApprox r
  bot : BotApprox r
  rogue : RogueApprox r
  consistent : ConsistentApprox r

end Factoid84
end DomainTheory.InformationSystems
