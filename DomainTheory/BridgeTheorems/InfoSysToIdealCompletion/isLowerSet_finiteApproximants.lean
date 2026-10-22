/-ai
The set of finite approximants of an element x is a lower set in the poset of finite elements.

If a finite element lies under a finite approximant of x, it lies under x, and every finite element below x is a finite approximant of x.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_of_mem_finiteApproximants

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem isLowerSet_finiteApproximants (x : A.Element) :
    IsLowerSet (finiteApproximants A x) := by
  intro y₁ y₂ hle hy₂
  exact mem_finiteApproximants_of_le A (le_trans hle (le_of_mem_finiteApproximants A hy₂))

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
