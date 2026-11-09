module

public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

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
