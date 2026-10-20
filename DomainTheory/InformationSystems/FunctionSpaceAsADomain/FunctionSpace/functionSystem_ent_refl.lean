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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion_singleton
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunEnt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- Function-space entailment is reflexive on members. -/
theorem functionSystem_ent_refl {w : Finset (FunToken A B)} {p : FunToken A B}
    (hw : FunCon A B w) (hp : p ∈ w) : FunEnt A B w p :=
  ⟨hw, {p},
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact hp,
    fun q hq => by
      cases Finset.mem_singleton.mp hq
      exact proposition_2_3_iii A p.property.1,
    by
      rw [funOutputUnion_singleton]
      exact proposition_2_3_iii B p.property.2⟩

end InfoSys

end DomainTheory.InformationSystems
