module

public import DomainTheory.BridgeTheorems.IsCompactElement
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.UpperLower.Basic
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
public import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_interpolate
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_subset
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_Ici_subset
public import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.isContinuousLattice_iff_isLUB_sInf_nhds

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Algebraicity: every element is the directed lub of compact elements below it. -/
class AlgebraicLattice (D : Type*) [CompleteLattice D] : Prop where
  out : ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

end IdealCompletionToContinuousLattice

end DomainTheory.BridgeTheorems
