module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_anti
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_nonempty
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes_directed
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter

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
    exact (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).2 ⟨b, hb, hab⟩
  · intro ha
    obtain ⟨b, hbS, hab⟩ := (wayBelow_sSup_iff (codes_nonempty f) (codes_directed f)).1 ha
    exact f.up_mem hbS ⟨a, rfl⟩ (wayBelowUp_anti hab.le)

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
