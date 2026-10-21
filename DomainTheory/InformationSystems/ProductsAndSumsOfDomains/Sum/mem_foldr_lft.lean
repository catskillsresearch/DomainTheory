/-ai
An element lies in the fold of left insertion over a multiset of sum tokens, starting from the empty set, if and only if that multiset contains the left token of the element.

Induct on the multiset. The empty multiset has empty fold and contains no token. If the head is a left token, membership in the inserted fold is equality with the inserted element or membership in the fold of the tail, and the inductive hypothesis matches a witness in the tail with a witness in the cons, while a witness at the head is that left token. If the head is a right token or the bottom, left insertion acts as the identity, so membership is membership in the tail fold; a witness in the tail remains a witness in the cons, and the head itself cannot be the desired left token.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_lft (s : Multiset (SumToken α β)) (x : α) :
    x ∈ Multiset.foldr lftInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | left a =>
      simp only [Multiset.foldr_cons, lftInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.left a, Or.inl rfl, congrArg SumToken.left hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx
          exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | right b =>
      simp only [Multiset.foldr_cons, lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, lftInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
