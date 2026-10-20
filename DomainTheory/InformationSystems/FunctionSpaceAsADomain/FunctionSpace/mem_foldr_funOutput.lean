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
