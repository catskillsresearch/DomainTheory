module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.le_of_mem_finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem toIdeal_mono {x y : A.Element} (hxy : x ≤ y) : toIdeal A x ≤ toIdeal A y := by
  intro z hz
  exact mem_finiteApproximants_of_le A
    (le_trans (le_of_mem_finiteApproximants A hz) hxy)

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
