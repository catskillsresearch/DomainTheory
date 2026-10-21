/-ai
Finitary union of finite sets of the codomain is associative.

Membership is compared in both directions, splitting on which summand contains the element.
ai-/

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

theorem funion_assoc' (a b c : Finset β) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl (mem_funion.mpr (Or.inr h)))
      · exact mem_funion.mpr (Or.inr h)

end InfoSys

end DomainTheory.InformationSystems
