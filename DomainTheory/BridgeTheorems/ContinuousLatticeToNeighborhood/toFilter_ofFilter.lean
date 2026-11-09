module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter

import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_ofFilter_of_round

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem toFilter_ofFilter {f : Filter (D := D)} (hr : Round f) :
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
