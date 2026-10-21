/-ai
If every input of a finite set of function-space tokens is entailed by a consistent set u', then the input union of that set is consistent.

The entailment of the input union by u' makes the union of u' with that input union consistent, and consistency passes to the right-hand summand.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.entSet_inputUnion_of_ent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion_con_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (hu' : u' ∈ A.Con) (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    funInputUnion A B s ∈ A.Con :=
  A.con_subset (proposition_2_3_ii A hu' (entSet_inputUnion_of_ent A B h))
    (subset_funion_right _ _)

end InfoSys

end DomainTheory.InformationSystems
