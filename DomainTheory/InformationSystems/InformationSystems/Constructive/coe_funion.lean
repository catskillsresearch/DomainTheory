module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.decidableEq_finset
public import DomainTheory.InformationSystems.InformationSystems.Constructive.insert_comm'
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_foldr_insert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion_empty_right

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

theorem coe_funion (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_funion]

end DomainTheory.InformationSystems.Constructive
