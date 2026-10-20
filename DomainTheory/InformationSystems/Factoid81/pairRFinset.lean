/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid81.TreeToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u
variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

private def pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairR t => insert t
  | .bot | .atom _ | .pairL _ => id

instance :
    LeftCommutative (pairRInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def pairRFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairRInsert (∅ : Finset (TreeToken α)) u.1

private theorem mem_foldr_pairR (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr pairRInsert (∅ : Finset (TreeToken α)) s ↔
      ∃ p ∈ s, p = .pairR t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairR a =>
      simp only [Multiset.foldr_cons, pairRInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairR a, Or.inl rfl, congrArg TreeToken.pairR ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairL _ =>
      simp only [Multiset.foldr_cons, pairRInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_pairRFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairRFinset u ↔ .pairR t ∈ u := by
  constructor
  · intro ht
    rcases (mem_foldr_pairR u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (mem_foldr_pairR u.1 t).2 ⟨.pairR t, Finset.mem_def.1 ht, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
