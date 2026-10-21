/-ai
An output token lies in the output union of a finite set of function tokens if and only if it lies in the output of some token of that set.

Unfolding the output union, the claim is the membership law for the fold of output-union applied to the underlying multiset of the set.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funOutputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_foldr_funOutput

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_funOutputUnion {s : Finset (FunToken A B)} {y : β} :
    y ∈ funOutputUnion A B s ↔ ∃ p ∈ s, y ∈ p.val.2 := by
  simpa [funOutputUnion] using mem_foldr_funOutput A B s.1 y

end InfoSys

end DomainTheory.InformationSystems
