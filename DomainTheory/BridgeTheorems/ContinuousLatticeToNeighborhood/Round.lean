module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpenu2eisUpperSet
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_univ
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_inter
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_sUnion
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
public import DomainTheory.ContinuousLattice.WayBelow.bot_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele_trans
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2esup
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_self_iff_scottOpen_Ici
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_sSup_iff
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_interpolate
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

/-- Roundness: `↟a ∈ f` is witnessed by a finer code `b` with `a ≪ b`. -/
class Round (f : Filter (D := D)) : Prop where
  out : ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
