module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
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
