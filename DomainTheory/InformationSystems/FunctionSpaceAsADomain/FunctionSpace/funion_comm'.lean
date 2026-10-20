module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funion_comm' (a b : Finset β) : a ∪' b = b ∪' a := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr h)
    · exact mem_funion.mpr (Or.inl h)

end InfoSys

end DomainTheory.InformationSystems
