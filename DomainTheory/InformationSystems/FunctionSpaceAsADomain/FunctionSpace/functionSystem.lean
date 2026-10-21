/-ai
Scott's Definition 7.1 packages the function space as an information system: the token is the bottom function token, consistency is function-space consistency, and entailment is function-space entailment. The information-system axioms are the downward-closure and singleton laws for consistency and the consistency, bottom, reflexivity, and transitivity laws for entailment.
ai-/

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

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

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
