/-ai
An element lies in the fold of right insertion over a multiset of sum tokens, starting from the empty set, if and only if that multiset contains the right token of the element.

Induct on the multiset. The empty multiset has empty fold and contains no token. If the head is a right token, membership in the inserted fold is equality with the inserted element or membership in the fold of the tail, and the inductive hypothesis matches a witness in the tail with a witness in the cons, while a witness at the head is that right token. If the head is a left token or the bottom, right insertion acts as the identity, so membership is membership in the tail fold; a witness in the tail remains a witness in the cons, and the head itself cannot be the desired right token.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtInsert
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

theorem mem_foldr_rht (s : Multiset (SumToken α β)) (y : β) :
    y ∈ Multiset.foldr rhtInsert (∅ : Finset β) s ↔ ∃ p ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | right b =>
      simp only [Multiset.foldr_cons, rhtInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hy | ⟨q, hq, hq'⟩)
        · exact ⟨.right b, Or.inl rfl, congrArg SumToken.right hy.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hy
          exact Or.inl hy.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | left a =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
