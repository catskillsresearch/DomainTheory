
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst7
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunInput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.instLeftCommutativeFunOutput
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_singleton
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.funInputUnion_funion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem funInputUnion_insert (s : Finset (FunToken A B)) (p : FunToken A B) :
    funInputUnion A B (insert p s) = p.val.1 ∪' funInputUnion A B s := by
  have h : insert p s = ({p} : Finset (FunToken A B)) ∪' s := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · exact mem_funion.mpr (Or.inl (hqp ▸ Finset.mem_singleton_self p))
      · exact mem_funion.mpr (Or.inr hq)
    · intro hq
      rcases mem_funion.mp hq with hq | hq
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hq))
      · exact Finset.mem_insert_of_mem hq
  rw [h, funInputUnion_funion, funInputUnion_singleton]

end InfoSys

end DomainTheory.InformationSystems
