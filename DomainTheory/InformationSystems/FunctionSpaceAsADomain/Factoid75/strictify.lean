module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_empty

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

/-- **Factoid 7.5.** Largest strict approximable map contained in `f` (Scott’s `strict`). -/
def strictify (f : ApproximableMap A B) : ApproximableMap A B where
  rel u v :=
    u ∈ A.Con ∧ v ∈ B.Con ∧
      (EmptyEntails B v ∨ (f.rel u v ∧ ¬ EmptyEntails A u))
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, B.con_empty, Or.inl (emptyEntails_empty B)⟩
  union_right := by
    rintro u v v' ⟨hu, hv, hvcase⟩ ⟨_, hv', hv'case⟩
    have hvU : v ∪' v' ∈ B.Con := by
      rcases hvcase with hE | ⟨hf, _⟩
      · rcases hv'case with hE' | ⟨hf', _⟩
        · exact B.con_subset
            (proposition_2_3_ii B B.con_empty (proposition_2_3_vi B hE hE'))
            (subset_funion_right _ _)
        · exact f.rel_cod (f.union_right
            (f.mono f.empty_rel (A.entSet_empty u) hE hu hv) hf')
      · rcases hv'case with hE' | ⟨hf', _⟩
        · exact f.rel_cod (f.union_right hf
            (f.mono f.empty_rel (A.entSet_empty u) hE' hu hv'))
        · exact f.rel_cod (f.union_right hf hf')
    refine ⟨hu, hvU, ?_⟩
    rcases hvcase with hE | ⟨hf, hn⟩
    · rcases hv'case with hE' | ⟨hf', hn'⟩
      · exact Or.inl (proposition_2_3_vi B hE hE')
      · exact Or.inr ⟨f.union_right
          (f.mono f.empty_rel (A.entSet_empty u) hE hu hv) hf', hn'⟩
    · rcases hv'case with hE' | ⟨hf', hn'⟩
      · exact Or.inr ⟨f.union_right hf
          (f.mono f.empty_rel (A.entSet_empty u) hE' hu hv'), hn⟩
      · exact Or.inr ⟨f.union_right hf hf', hn⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, hcase⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    rcases hcase with hE | ⟨hf, hn⟩
    · exact Or.inl (fun y hy => B.ent_trans B.con_empty hv hE (hEntv y hy))
    · refine Or.inr ⟨f.mono hf hEntu hEntv hu' hv', fun hE' => hn ?_⟩
      exact fun x hx => A.ent_trans A.con_empty hu' hE' (hEntu x hx)

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
