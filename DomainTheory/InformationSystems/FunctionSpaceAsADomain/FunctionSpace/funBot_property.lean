
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- The empty pair is a function-space token. -/
theorem funBot_property : (∅ : Finset α) ∈ A.Con ∧ (∅ : Finset β) ∈ B.Con :=
  ⟨A.con_empty, B.con_empty⟩

end InfoSys

end DomainTheory.InformationSystems
