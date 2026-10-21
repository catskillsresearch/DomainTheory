/-ai
The extended presentation equivalence of a continuous lattice lands in those ideals of finite elements of the way-below information system that come from round information-system elements. It is the composite of the presentation-domains equivalence and the isomorphism from round information-system elements to that part of the ideal completion.
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
public import DomainTheory.BridgeTheorems.PresentationDomains.IsRoundInfoSysElement
public import DomainTheory.BridgeTheorems.PresentationDomains.roundInfoSys_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv

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

/-- Extended form through ideal completion of finite elements of the `↟`-InfoSys. -/
noncomputable def presentation_domains_equiv_ideal :
    D ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } :=
  (presentation_domains_equiv hD).trans (roundInfoSys_ideal_iso (D := D))

end Continuous

end DomainTheory.BridgeTheorems
