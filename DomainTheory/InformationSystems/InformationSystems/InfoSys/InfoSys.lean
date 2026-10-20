/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic

@[expose] public section

universe u

namespace DomainTheory.InformationSystems

/-- A Scott information system on a type of tokens `α`, following Scott's Definition 2.1
in *"Domains for Denotational Semantics"* (ICALP 1982).

`DecidableEq α` is required so that finite token sets support union (`X ∪ {a}`) and the
other `Finset` operations the axioms mention. -/
structure InfoSys (α : Type u) [DecidableEq α] where
  /-- The distinguished least-informative object `Δ`. -/
  bot : α
  /-- The consistent finite sets of tokens. -/
  Con : Set (Finset α)
  /-- Entailment: `Ent u a` means the consistent set `u` forces the token `a`. -/
  Ent : Finset α → α → Prop
  /-- (i) Consistency is downward closed under `⊆`. -/
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  /-- (ii) Every singleton is consistent. -/
  con_sing : ∀ a : α, {a} ∈ Con
  /-- (iii) A set entailing `a` stays consistent when `a` is added. Scott writes this as
  `u ∪ {a} ∈ Con`; we use the definitionally identical `insert a u`, because mathlib's
  `Finset` union instance (unlike `insert`) depends on `Classical.choice`, which would
  break the constructive development. -/
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  /-- (iv) The least token `Δ` is entailed by every consistent set. -/
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  /-- (v) Entailment is reflexive on members of a consistent set. -/
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  /-- (vi) Entailment is transitive (cut): if a consistent `v` entails every member of a
  consistent `u`, and `u ⊢ c`, then `v ⊢ c`. -/
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

end DomainTheory.InformationSystems
