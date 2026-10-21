/-ai
The order isomorphism between round way-below filters and round elements of the coded information system applies the domain isomorphism of the way-below neighbourhood basis, and the inverse applies its inverse. Roundness of a filter is roundness of the filter recovered by cancelling the isomorphism with its inverse, and roundness of an information-system element is already the roundness of the corresponding filter. The two composites are the identity on the underlying elements, and the order comparison is that of the domain isomorphism.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis
public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open Order

open scoped DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

universe u

variable {D : Type u} [CompleteLattice D] [DecidableEq D]

/-- Round `↟`-filters ↔ round elements of the coded InfoSys. -/
noncomputable def roundFilter_infoSys_iso :
    RoundFilter (D := D) ≃o RoundInfoSysElement (D := D) where
  toFun := fun f =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso f.1, by
      let f' : (wayBelowNbhdBasis (D := D)).system.Element := f.1
      change IsRound ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm
        ((wayBelowNbhdBasis (D := D)).domainOrderIso f'))
      rw [OrderIso.symm_apply_apply]
      exact f.2⟩
  invFun := fun e =>
    ⟨(wayBelowNbhdBasis (D := D)).domainOrderIso.symm e.1, e.2⟩
  left_inv := fun f => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.left_inv f.1
  right_inv := fun e => Subtype.ext <|
    (wayBelowNbhdBasis (D := D)).domainOrderIso.right_inv e.1
  map_rel_iff' := by
    intro f g
    exact (wayBelowNbhdBasis (D := D)).domainOrderIso.map_rel_iff

end DomainTheory.BridgeTheorems
