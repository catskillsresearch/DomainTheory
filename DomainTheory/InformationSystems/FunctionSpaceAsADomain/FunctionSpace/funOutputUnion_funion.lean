module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_funOutputUnion

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funOutputUnion_funion (s t : Finset (FunToken A B)) :
    funOutputUnion A B (s ∪' t) = funOutputUnion A B s ∪' funOutputUnion A B t := by
  ext y
  constructor
  · intro hy
    rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
    rcases mem_funion.mp hp with hp | hp
    · exact mem_funion.mpr (Or.inl ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
    · exact mem_funion.mpr (Or.inr ((mem_funOutputUnion A B).2 ⟨p, hp, hy'⟩))
  · intro hy
    rcases mem_funion.mp hy with hy | hy
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inl hp), hy'⟩
    · rcases (mem_funOutputUnion A B).1 hy with ⟨p, hp, hy'⟩
      exact (mem_funOutputUnion A B).2 ⟨p, mem_funion.mpr (Or.inr hp), hy'⟩

end InfoSys

end DomainTheory.InformationSystems
