module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

universe u

namespace DomainTheory.InformationSystems

structure InfoSys (α : Type u) [DecidableEq α] where

  bot : α

  Con : Set (Finset α)

  Ent : Finset α → α → Prop

  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con

  con_sing : ∀ a : α, {a} ∈ Con

  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con

  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot

  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a

  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

end DomainTheory.InformationSystems
