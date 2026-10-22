module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_funion
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

@[simp] theorem funion_empty_right (u : Finset α) : u ∪' (∅ : Finset α) = u := by
  ext x
  simp only [mem_funion, Finset.notMem_empty, or_false]

end DomainTheory.InformationSystems.Constructive
