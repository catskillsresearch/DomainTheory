module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_ofFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_isRound
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.RoundFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter_mono
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
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
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.ofFilter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : ContinuousLattice D)

include hD

/-- Order-isomorphism: continuous lattice ↔ round `↟`-filters. -/
noncomputable def domainOrderIso : D ≃o RoundFilter (D := D) where
  toFun x := ⟨toFilter x, toFilter_isRound hD x⟩
  invFun f := ofFilter (D := D) f.1
  left_inv x := ofFilter_toFilter hD x
  right_inv f := Subtype.ext (toFilter_ofFilter f.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      have : ofFilter (toFilter x) ≤ ofFilter (toFilter y) := by
        refine sSup_le fun a ha => ?_
        have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
        exact le_sSup (h (wayBelowUp a) ⟨a, ⟨rfl, ha'⟩⟩)
      simpa [ofFilter_toFilter hD] using this
    · intro hxy
      exact toFilter_mono hxy

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
