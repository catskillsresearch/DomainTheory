module

public import DomainTheory.BridgeTheorems.toFilter
public import DomainTheory.BridgeTheorems.ofFilter
public import DomainTheory.BridgeTheorems.mem_basicOpen_iff
import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.NeighbourhoodSystems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem toFilter_ofFilter (f : (toNeighborhoodSystem A).Element) :
    toFilter A (ofFilter A f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem A) fun U => ?_
  constructor
  · intro h
    obtain ⟨u, hu, hU, hsub⟩ := h
    subst hU
    exact (mem_basicOpen_iff A f hu).mpr hsub
  · intro hU
    obtain ⟨u, hu, heq⟩ := f.sub hU
    subst heq
    exact ⟨u, hu, rfl, (mem_basicOpen_iff A f hu).mp hU⟩

end InfoSysToNeighborhood

end DomainTheory.BridgeTheorems
