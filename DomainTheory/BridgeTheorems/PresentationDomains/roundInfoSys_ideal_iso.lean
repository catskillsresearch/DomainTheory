/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis
public import DomainTheory.BridgeTheorems.PresentationDomains.IsRoundInfoSysElement
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

section Continuous

variable (hD : IsContinuousLattice D)

include hD

/-- Round InfoSys elements ↔ ideals of finite elements that come from round InfoSys
elements (via the ideal-completion iso). -/
noncomputable def roundInfoSys_ideal_iso :
    RoundInfoSysElement (D := D) ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } := by
  let A := (wayBelowNbhdBasis (D := D)).toInfoSys
  let ιE := InfoSysToIdealCompletion.domainOrderIso A
  refine {
    toFun := fun e => ⟨ιE e.1, by
      change IsRoundInfoSysElement (ιE.symm (ιE e.1))
      rw [OrderIso.symm_apply_apply]
      exact e.2⟩
    invFun := fun I => ⟨ιE.symm I.1, I.2⟩
    left_inv := fun e => Subtype.ext (ιE.left_inv e.1)
    right_inv := fun I => Subtype.ext (ιE.right_inv I.1)
    map_rel_iff' := by
      intro e₁ e₂
      exact ιE.map_rel_iff
  }

end Continuous

end DomainTheory.BridgeTheorems
