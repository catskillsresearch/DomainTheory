/-ai
A sum token lies in the fold that inserts the left constructor of each member of a multiset s if and only if it is the left constructor of some member of s.

Induction on the multiset. The empty multiset yields the empty set, which has no members and supplies no witness. For a cons cell, membership after insertion is the head equation or membership in the inductive fold, and membership in the cons multiset is the head or membership in the tail, and the two disjunctions correspond in both directions.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_liftSumLeft (s : Multiset α) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ x ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

end InfoSys

end DomainTheory.InformationSystems
