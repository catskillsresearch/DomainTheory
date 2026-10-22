module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_foldr_insert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

@[simp] theorem mem_funion {a : α} {u v : Finset α} :
    a ∈ u ∪' v ↔ a ∈ u ∨ a ∈ v := mem_foldr_insert a u v.1

end DomainTheory.InformationSystems.Constructive
