module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_directed
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_nonempty
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_anti
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpenu2eisUpperSet
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_subset
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_Ici_subset
public import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.isContinuousLattice_iff_isLUB_sInf_nhds
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem mem_wayBelowUp_ofFilter_of_round {f : Filter (D := D)} (hr : Round f) {a : D} :
    f.mem (wayBelowUp a) ↔ a ≪ ofFilter f := by
  constructor
  · intro ha
    obtain ⟨b, hab, hb⟩ := hr.out ha
    exact (WayBelow.sSup_iff (codes_nonempty f) (codes_directed f)).2 ⟨b, hb, hab⟩
  · intro ha
    obtain ⟨b, hbS, hab⟩ := (WayBelow.sSup_iff (codes_nonempty f) (codes_directed f)).1 ha
    exact f.up_mem hbS ⟨a, rfl⟩ (wayBelowUp_anti hab.le)

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
