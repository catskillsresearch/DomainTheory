/-ai
For finite sets a, b, and c of input tokens, the choice-free union satisfies a ∪' (b ∪' c) = b ∪' (a ∪' c).

Extensionality reduces the equation to membership. In each direction, membership in a choice-free union is split twice, and the three alternatives are reassembled so that b is the outer summand and a is nested in the second union.
ai-/
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

theorem funion_left_comm (a b c : Finset α) :
    a ∪' (b ∪' c) = b ∪' (a ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inl h)))
    · rcases mem_funion.mp h with h | h
      · exact mem_funion.mpr (Or.inl h)
      · exact mem_funion.mpr (Or.inr (mem_funion.mpr (Or.inr h)))

end InfoSys

end DomainTheory.InformationSystems
