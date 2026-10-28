module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)
universe u v

theorem funBot.property : (∅ : Finset α) ∈ A.Con ∧ (∅ : Finset β) ∈ B.Con :=
  ⟨A.con_empty, B.con_empty⟩

def funBot : FunToken A B :=
  ⟨(∅, ∅), funBot.property A B⟩

end InfoSys

end DomainTheory.InformationSystems
