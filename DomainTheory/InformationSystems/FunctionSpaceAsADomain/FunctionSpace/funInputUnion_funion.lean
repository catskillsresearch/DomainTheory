/-ai
The input union of a finitary union of two finite sets of function-space tokens is the finitary union of the two input unions.

Membership is compared in both directions. A member of the input union of the combined set lies in the input of a token from one side or the other, and conversely a member of either input union arises from a token of the corresponding side of the combined set.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_funInputUnion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion_funion (s t : Finset (FunToken A B)) :
    funInputUnion A B (s ∪' t) = funInputUnion A B s ∪' funInputUnion A B t := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funInputUnion A B).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.mp hx with hx | hx
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hx'⟩
    · rcases (mem_funInputUnion A B).1 hx with ⟨p, hp, hx'⟩
      exact (mem_funInputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hx'⟩

end InfoSys

end DomainTheory.InformationSystems
