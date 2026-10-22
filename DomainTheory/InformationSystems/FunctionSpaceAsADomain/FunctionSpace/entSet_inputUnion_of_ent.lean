
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

theorem entSet_inputUnion_of_ent {u' : Finset α} {s : Finset (FunToken A B)}
    (h : ∀ q ∈ s, A.EntSet u' q.val.1) :
    A.EntSet u' (funInputUnion A B s) := by
  intro x hx
  rcases (mem_funInputUnion A B).1 hx with ⟨q, hq, hx'⟩
  exact h q hq x hx'

end InfoSys

end DomainTheory.InformationSystems
