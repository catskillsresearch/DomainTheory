/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_con_of_ent
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.exists_combined_witness

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Function-space entailment is transitive. -/
theorem functionSystem_ent_trans {u v : Finset (FunToken A B)} {c : FunToken A B}
    (hv : FunCon A B v) (hu : FunCon A B u)
    (hEnts : ∀ y ∈ u, FunEnt A B v y) (hEnt : FunEnt A B u c) :
    FunEnt A B v c := by
  obtain ⟨_, s, hs, hEntIn, hEntOut⟩ := hEnt
  refine ⟨hv, ?_⟩
  have hWit : ∀ q ∈ s, ∃ s_q ⊆ v, (∀ r ∈ s_q, A.EntSet q.val.1 r.val.1) ∧
      B.EntSet (funOutputUnion A B s_q) q.val.2 := by
    intro q hq
    exact (hEnts q (hs hq)).2
  obtain ⟨S, hSsub, hSin, hSout⟩ :=
    exists_combined_witness A B hv c.property.1 hEntIn hWit
  refine ⟨S, hSsub, hSin, ?_⟩
  have hin_s : funInputUnion A B s ∈ A.Con :=
    funInputUnion_con_of_ent A B c.property.1 hEntIn
  have hout_s : funOutputUnion A B s ∈ B.Con := hu s hs hin_s
  have hin_S : funInputUnion A B S ∈ A.Con :=
    funInputUnion_con_of_ent A B c.property.1 hSin
  have hout_S : funOutputUnion A B S ∈ B.Con := hv S hSsub hin_S
  exact proposition_2_3_iv B hout_S hout_s hSout hEntOut

end InfoSys

end DomainTheory.InformationSystems
