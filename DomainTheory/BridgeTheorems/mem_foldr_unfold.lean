/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.Factoid81
public import DomainTheory.BridgeTheorems.unfoldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_foldr_unfold (m : Multiset (TreeToken α))
    (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    s ∈ Multiset.foldr (unfoldInsert A) ∅ m ↔
      ∃ t ∈ m, treeUnfold A t = s := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro hs; exact False.elim (Finset.notMem_empty s hs)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro t rest ih
    simp only [Multiset.foldr_cons, unfoldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨t, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

end DomainTheory.BridgeTheorems
