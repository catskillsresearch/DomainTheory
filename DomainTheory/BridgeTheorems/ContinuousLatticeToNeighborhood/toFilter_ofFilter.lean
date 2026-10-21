/-ai
If a filter f is round, the principal filter of its retraction equals f.

The two filters are compared neighbourhood by neighbourhood. A way-below neighbourhood in the principal filter has code way-below the retraction, hence belongs to f by the round-filter characterization. Conversely, every neighbourhood in f is the way-below neighbourhood of some code, and that membership means the code is way-below the retraction, so the neighbourhood belongs to the principal filter.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.IsRound
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_ofFilter_of_round

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem toFilter_ofFilter {f : Filter (D := D)} (hr : IsRound f) :
    toFilter (ofFilter f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem) fun U => ?_
  constructor
  · intro hU
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    exact (mem_wayBelowUp_ofFilter_of_round hr).2 ha
  · intro hU
    obtain ⟨a, rfl⟩ := f.sub hU
    refine ⟨a, ⟨rfl, ?_⟩⟩
    exact (mem_wayBelowUp_ofFilter_of_round hr).1 hU

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
