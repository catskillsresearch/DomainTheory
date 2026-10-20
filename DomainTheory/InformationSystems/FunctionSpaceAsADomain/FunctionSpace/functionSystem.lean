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
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_con_subset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_con_sing
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_ent_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_ent_bot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_ent_refl
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem_ent_trans

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- **Definition 7.1.** The function-space information system `A → B`. -/
def functionSystem : InfoSys (FunToken A B) where
  bot := funBot A B
  Con := {w | FunCon A B w}
  Ent := FunEnt A B
  con_subset := functionSystem_con_subset A B
  con_sing := functionSystem_con_sing A B
  ent_con := functionSystem_ent_con A B
  ent_bot := functionSystem_ent_bot A B
  ent_refl := functionSystem_ent_refl A B
  ent_trans := functionSystem_ent_trans A B

end InfoSys

end DomainTheory.InformationSystems
