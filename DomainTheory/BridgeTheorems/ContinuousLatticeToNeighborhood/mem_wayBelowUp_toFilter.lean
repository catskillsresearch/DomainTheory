module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem mem_wayBelowUp_toFilter {x a : D} :
    (toFilter x).mem (wayBelowUp a) ↔ a ≪ x := by
  constructor
  · intro h
    obtain ⟨b, ⟨heq, hb⟩⟩ := h
    have : x ∈ wayBelowUp b := hb
    rwa [← heq] at this
  · intro ha
    exact ⟨a, ⟨rfl, ha⟩⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
