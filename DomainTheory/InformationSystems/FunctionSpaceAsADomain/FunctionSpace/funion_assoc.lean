
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

theorem funion_assoc (a b c : Finset α) :
    (a ∪' b) ∪' c = a ∪' (b ∪' c) := by
  ext x
  constructor
  · intro hx
    rcases funion.mem.mp hx with h | h
    · rcases funion.mem.mp h with h | h
      · exact funion.mem.mpr (Or.inl h)
      · exact funion.mem.mpr (Or.inr (funion.mem.mpr (Or.inl h)))
    · exact funion.mem.mpr (Or.inr (funion.mem.mpr (Or.inr h)))
  · intro hx
    rcases funion.mem.mp hx with h | h
    · exact funion.mem.mpr (Or.inl (funion.mem.mpr (Or.inl h)))
    · rcases funion.mem.mp h with h | h
      · exact funion.mem.mpr (Or.inl (funion.mem.mpr (Or.inr h)))
      · exact funion.mem.mpr (Or.inr h)

end InfoSys

end DomainTheory.InformationSystems
