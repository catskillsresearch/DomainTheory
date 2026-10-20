/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62
public import DomainTheory.InformationSystems.Factoid32
public import DomainTheory.InformationSystems.Theorem72.rel_input_output_union

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- Deductive closure of the token-set of an approximable map. -/
theorem approxMap_toElement_closed (f : ApproximableMap A B)
    (Y : Finset (FunToken A B)) (p : FunToken A B)
    (hY : (Y : Set (FunToken A B)) ⊆ {p : FunToken A B | f.rel p.val.1 p.val.2})
    (hEnt : (functionSystem A B).Ent Y p) :
    p ∈ {q : FunToken A B | f.rel q.val.1 q.val.2} := by
  obtain ⟨_hCon, s, hs, hEntIn, hEntOut⟩ := hEnt
  have hrel : ∀ q ∈ s, f.rel q.val.1 q.val.2 := fun q hq =>
    hY (Finset.mem_coe.2 (hs hq))
  have hin_s : funInputUnion A B s ∈ A.Con :=
    A.con_subset
      (proposition_2_3_ii A p.property.1 (entSet_inputUnion_of_ent A B hEntIn))
      (subset_funion_right _ _)
  have hIO := rel_input_output_union A B f s hrel hin_s
  have hU : f.rel p.val.1 (funOutputUnion A B s) :=
    f.mono hIO (entSet_inputUnion_of_ent A B hEntIn)
      (proposition_2_3_iii B (f.rel_cod hIO)) p.property.1 (f.rel_cod hIO)
  exact f.mono hU (proposition_2_3_iii A p.property.1) hEntOut p.property.1 p.property.2

end InfoSys

end DomainTheory.InformationSystems
