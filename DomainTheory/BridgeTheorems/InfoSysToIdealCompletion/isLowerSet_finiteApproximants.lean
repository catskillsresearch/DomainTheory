module

public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import Mathlib.Order.UpperLower.Basic
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_of_mem_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem isLowerSet_finiteApproximants (x : A.Element) :
    IsLowerSet (finiteApproximants A x) := by
  intro y₁ y₂ hle hy₂
  exact mem_finiteApproximants_of_le A (le_trans hle (le_of_mem_finiteApproximants A hy₂))

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
