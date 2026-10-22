module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- Principal filter of `↟`-neighbourhoods at `x`. -/
def toFilter (x : D) : Filter (D := D) where
  mem U := ∃ a : D, U = wayBelowUp a ∧ a ≪ x
  sub := by
    intro U h
    obtain ⟨a, ⟨rfl, _⟩⟩ := h
    exact ⟨a, rfl⟩
  master_mem := ⟨⊥, wayBelowUp_bot.symm, bot_wayBelow x⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, ⟨rfl, hb⟩⟩ := hV
    exact ⟨a ⊔ b, ⟨wayBelowUp_inter a b, WayBelow.sup ha hb⟩⟩
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
    obtain ⟨b, rfl⟩ := hV
    exact ⟨b, ⟨rfl, hUV ha⟩⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
