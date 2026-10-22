/-ai
Factoid 4.6 gives the order isomorphism between the approximable maps from an information system to another and the Scott-continuous maps of their domains. It sends an approximable map to the associated Scott-continuous map and conversely, and the two composites are the identity. One approximable map lies under another exactly when the associated Scott-continuous map does, because the order of approximable maps is the order of the elements they determine.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.ConjScottMap
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9
public import DomainTheory.BridgeTheorems.ofScottContinuous_toScottContinuous
public import DomainTheory.BridgeTheorems.toScottContinuous_ofScottContinuous

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- **Factoid 4.6.** Approximable maps ↔ Scott-continuous maps of domains. -/
noncomputable def approximableMap_scottContinuous_equiv (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o ScottContinuous A B where
  toFun := toScottContinuous
  invFun := ofScottContinuous
  left_inv := ofScottContinuous_toScottContinuous
  right_inv := toScottContinuous_ofScottContinuous
  map_rel_iff' := by
    intro f g
    exact (le_iff_toElement_le f g).symm

end DomainTheory.BridgeTheorems
