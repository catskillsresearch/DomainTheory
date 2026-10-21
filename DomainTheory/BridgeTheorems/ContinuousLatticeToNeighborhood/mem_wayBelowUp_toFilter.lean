/-ai
The way-below neighbourhood of a belongs to the principal filter of x if and only if a is way-below x.

Membership supplies a code b whose neighbourhood equals that of a and which is way-below x, and rewriting the membership of x along that equality gives the claim. Conversely, a itself is the required code.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter

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
