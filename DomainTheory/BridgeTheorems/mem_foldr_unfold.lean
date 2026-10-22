/-ai
A sum token lies in the multiset fold of unfold insertion over a multiset of tree tokens if and only if it is the tree unfold of some member of the multiset.

The proof is by induction on the multiset. The empty fold is empty, so both sides fail. At a cons cell, membership in the inserted fold is equality with the unfold of the head or membership in the fold of the tail, which matches membership in the cons multiset.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.unfoldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10

@[expose] public section

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
