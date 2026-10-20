module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : IsContinuousLattice D)

include hD

theorem ofFilter_toFilter (x : D) : ofFilter (toFilter x) = x := by
  have hset : codes (toFilter x) = {a : D | a ≪ x} := by
    ext a
    exact mem_wayBelowUp_toFilter
  change sSup (codes (toFilter x)) = x
  rw [hset, hD.sSup_wayBelow x]

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
