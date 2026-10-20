/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- **Proposition 5.4(i).** Identity approximable mapping given by entailment. -/
def idMap : ApproximableMap A A where
  rel u v := u ∈ A.Con ∧ v ∈ A.Con ∧ A.EntSet u v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel := ⟨A.con_empty, A.con_empty, A.entSet_empty ∅⟩
  union_right := by
    rintro u v v' ⟨hu, _hv, huv⟩ ⟨_, _hv', huv'⟩
    have hEnt : A.EntSet u (v ∪' v') := proposition_2_3_vi (sys := A) huv huv'
    have hBig : u ∪' (v ∪' v') ∈ A.Con :=
      proposition_2_3_ii (sys := A) (u := u) (v := v ∪' v') hu hEnt
    have hCon : v ∪' v' ∈ A.Con :=
      A.con_subset hBig (subset_funion_right u (v ∪' v'))
    exact ⟨hu, hCon, hEnt⟩
  mono := by
    rintro u u' v v' ⟨hu, hv, huv⟩ hEntu hEntv hu' hv'
    refine ⟨hu', hv', ?_⟩
    exact proposition_2_3_iv A hu' hv
      (proposition_2_3_iv A hu' hu hEntu huv) hEntv

end InfoSys

end DomainTheory.InformationSystems
