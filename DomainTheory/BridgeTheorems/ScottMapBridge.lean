module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.ConjScottMap
public import DomainTheory.BridgeTheorems.approximableMap_scottContinuous_equiv
public import DomainTheory.BridgeTheorems.conjScottMapFun
public import DomainTheory.BridgeTheorems.orderIso
public import DomainTheory.BridgeTheorems.scottContinuous_ext
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9
public import DomainTheory.BridgeTheorems.ofScottContinuous_toScottContinuous
public import DomainTheory.BridgeTheorems.toScottContinuous_ofScottContinuous
public import DomainTheory.BridgeTheorems.conjScottMapFun_le_iff
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst19
public import DomainTheory.BridgeTheorems.ext
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst21

@[expose] public section

/-!
# Construction cross-links — ApproximableMap ↔ ScottContinuous ↔ ScottMap

* **Factoid 4.6:** `ApproximableMap A B ≃o ScottContinuous A B` (1982).
* **1972 transport:** `ScottMap D D'` conjugates along `presentation_domains_equiv`
  (or the round-filter iso) to pointwise-ordered maps on the round presentation.
* Blueprint packaging: `infoSys_constructions_equiv` bundles the three 1982 domain
  isos with these cross-links.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open DomainTheory.ContinuousLattice
open ContinuousLatticeToNeighborhood

/-! ## Factoid 4.6 as an order isomorphism -/

variable {α β : Type*} [DecidableEq α] [DecidableEq β]






/-! ## ScottMap conjugation along the round presentation -/

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]




namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
variable (ιD : D ≃o D') (ιE : E ≃o E')





end ConjScottMap

section ContinuousRoundFilter

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
include hD hE

/-- Conjugation along round `↟`-filters (no `DecidableEq` needed). -/
noncomputable abbrev scottMap_roundFilter_iso :
    ScottMap D E ≃o
      ConjScottMap (continuousLattice_roundFilter_iso hD)
        (continuousLattice_roundFilter_iso hE) :=
  ConjScottMap.orderIso (continuousLattice_roundFilter_iso hD)
    (continuousLattice_roundFilter_iso hE)

end ContinuousRoundFilter

section ContinuousRoundInfoSys

variable (hD : IsContinuousLattice D) (hE : IsContinuousLattice E)
variable [DecidableEq D] [DecidableEq E]
include hD hE

/-- Conjugation along round InfoSys elements of the `↟`-basis. -/
noncomputable abbrev scottMap_roundInfoSys_iso :
    ScottMap D E ≃o
      ConjScottMap (presentation_domains_equiv hD) (presentation_domains_equiv hE) :=
  ConjScottMap.orderIso (presentation_domains_equiv hD) (presentation_domains_equiv hE)

end ContinuousRoundInfoSys

/-! ## Blueprint packaging

Bundled 1982 construction domain isos + 1972/1982 function-space cross-links. -/
namespace infoSys_constructions_equiv

noncomputable abbrev product := @infoSys_product_domain_equiv
noncomputable abbrev sum := @infoSys_sum_domain_equiv
noncomputable abbrev functionSpace := @infoSys_function_space_domain_equiv
noncomputable abbrev approximable_scottContinuous := @approximableMap_scottContinuous_equiv
noncomputable abbrev scottMap_roundFilter := @scottMap_roundFilter_iso
noncomputable abbrev scottMap_roundInfoSys := @scottMap_roundInfoSys_iso

end infoSys_constructions_equiv

end DomainTheory.BridgeTheorems
