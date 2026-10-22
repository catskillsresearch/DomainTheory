/-ai
A tree token lies in the multiset fold of fold insertion over a multiset of sum tokens if and only if it is the tree fold of some member of the multiset.

The proof is by induction on the multiset. The empty fold is empty, so both sides fail. At a cons cell, membership in the inserted fold is equality with the fold of the head or membership in the fold of the tail, which matches membership in the cons multiset.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.foldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem mem_foldr_fold
    (m : Multiset (SumToken α (ProdToken (treeSystem A) (treeSystem A))))
    (t : TreeToken α) :
    t ∈ Multiset.foldr (foldInsert A) ∅ m ↔
      ∃ s ∈ m, treeFold A s = t := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro s rest ih
    simp only [Multiset.foldr_cons, foldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨s, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

end DomainTheory.BridgeTheorems
