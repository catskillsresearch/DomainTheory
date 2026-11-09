module

public import DomainTheory.BridgeTheorems.approximableMap_scottContinuous_equiv
public import DomainTheory.BridgeTheorems.orderIso
public import DomainTheory.BridgeTheorems.PresentationDomains.presentation_domains_equiv
public import DomainTheory.BridgeTheorems.InfoSysConstructions.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

noncomputable abbrev scottMap_roundFilter_iso (hD : ContinuousLattice D) (hE : ContinuousLattice E) :
    ScottMap D E ≃o
      ConjScottMap (continuousLattice_roundFilter_iso hD)
        (continuousLattice_roundFilter_iso hE) :=
  ConjScottMap.orderIso (continuousLattice_roundFilter_iso hD)
    (continuousLattice_roundFilter_iso hE)

variable [DecidableEq D] [DecidableEq E]

noncomputable abbrev scottMap_roundInfoSys_iso (hD : ContinuousLattice D) (hE : ContinuousLattice E) :
    ScottMap D E ≃o
      ConjScottMap (presentation_domains_equiv hD) (presentation_domains_equiv hE) :=
  ConjScottMap.orderIso (presentation_domains_equiv hD) (presentation_domains_equiv hE)

namespace infoSys_constructions_equiv

noncomputable abbrev product := @infoSys_product_domain_equiv
noncomputable abbrev sum := @infoSys_sum_domain_equiv
noncomputable abbrev functionSpace := @infoSys_function_space_domain_equiv
noncomputable abbrev approximable_scottContinuous := @approximableMap_scottContinuous_equiv
noncomputable abbrev scottMap_roundFilter := @scottMap_roundFilter_iso
noncomputable abbrev scottMap_roundInfoSys := @scottMap_roundInfoSys_iso

end infoSys_constructions_equiv

end DomainTheory.BridgeTheorems
