/-ai
An input token lies in the fold of choice-free input-union over a multiset of function tokens, starting from the empty set, if and only if it lies in the input of some token of the multiset.

The proof is by induction on the multiset. The empty fold is empty, so neither side holds. For a cons, membership in the folded union splits into membership in the head input or membership in the fold of the tail, and membership in the multiset splits into equality with the head or membership in the tail; the induction hypothesis matches the two sides.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_funInput (t : Multiset (FunToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : FunToken A B => funion p.val.1) (∅ : Finset α) t ↔
      ∃ p ∈ t, x ∈ p.val.1 := by
  refine Multiset.induction_on t ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, mem_funion, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hx⟩)
      · exact ⟨p, Or.inl rfl, hx⟩
      · exact ⟨q, Or.inr hq, hx⟩
    · rintro ⟨q, hq, hx⟩
      rcases hq with rfl | hq
      · exact Or.inl hx
      · exact Or.inr ⟨q, hq, hx⟩

end InfoSys

end DomainTheory.InformationSystems
