/-ai
The input union of a singleton function-space token is the input component of that token.

Membership is compared in both directions. A member of the input union belongs to the input of the unique token of the singleton, and conversely that input is recovered from singleton membership.
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

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion_singleton (p : FunToken A B) :
    funInputUnion A B {p} = p.val.1 := by
  ext x
  constructor
  · intro hx
    rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
    have : q = p := Finset.mem_singleton.mp hq
    subst this
    exact hx'
  · intro hx
    exact (mem_funInputUnion A B).2 ⟨p, Finset.mem_singleton_self p, hx⟩

end InfoSys

end DomainTheory.InformationSystems
