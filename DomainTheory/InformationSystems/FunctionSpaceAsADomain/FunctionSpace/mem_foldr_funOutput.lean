/-ai
An output token lies in the fold of choice-free output-union over a multiset of function tokens, starting from the empty set, if and only if it lies in the output of some token of the multiset.

The proof is by induction on the multiset. The empty fold is empty, so neither side holds. For a cons, membership in the folded union splits into membership in the head output or membership in the fold of the tail, and membership in the multiset splits into equality with the head or membership in the tail; the induction hypothesis matches the two sides.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_funOutput (t : Multiset (FunToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.2) (∅ : Finset β) t ↔
      ∃ p ∈ t, y ∈ p.val.2 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, mem_funion, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hy⟩)
      · exact ⟨p, Or.inl rfl, hy⟩
      · exact ⟨q, Or.inr hq, hy⟩
    · rintro ⟨q, hq, hy⟩
      rcases hq with rfl | hq
      · exact Or.inl hy
      · exact Or.inr ⟨q, hq, hy⟩

end InfoSys

end DomainTheory.InformationSystems
