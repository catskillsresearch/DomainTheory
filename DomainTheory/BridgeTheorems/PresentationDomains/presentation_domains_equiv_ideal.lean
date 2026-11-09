module

public import DomainTheory.BridgeTheorems.PresentationDomains.roundInfoSys_ideal_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv

@[expose] public section

namespace DomainTheory.BridgeTheorems

open Order

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

noncomputable def presentation_domains_equiv_ideal (hD : ContinuousLattice D) :
    D ≃o
      { I : Ideal (InfoSysToIdealCompletion.FiniteElement
          (wayBelowNbhdBasis (D := D)).toInfoSys) //
        IsRoundInfoSysElement (D := D)
          ((InfoSysToIdealCompletion.domainOrderIso
            (wayBelowNbhdBasis (D := D)).toInfoSys).symm I) } :=
  (presentation_domains_equiv hD).trans (roundInfoSys_ideal_iso (D := D))

end DomainTheory.BridgeTheorems
