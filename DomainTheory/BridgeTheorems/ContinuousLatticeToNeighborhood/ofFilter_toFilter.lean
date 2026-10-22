/-ai
If a complete lattice D is continuous, the retraction of the principal filter of an element x equals x.

The codes of that principal filter are exactly the elements way-below x, and continuity says that the supremum of the elements way-below x is x.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : ContinuousLattice D)

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
