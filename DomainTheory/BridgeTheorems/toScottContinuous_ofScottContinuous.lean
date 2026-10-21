/-ai
Passing a Scott-continuous map through ofScottContinuous and then toScottContinuous returns the original map.

The two maps agree as functions because the information-system element of a value is recovered from the approximable relation, so extensionality of Scott-continuous maps gives the equality.
ai-/
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
public import DomainTheory.BridgeTheorems.scottContinuous_ext
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem toScottContinuous_ofScottContinuous {A : InfoSys α} {B : InfoSys β}
    (g : ScottContinuous A B) :
    toScottContinuous (ofScottContinuous g) = g :=
  scottContinuous_ext fun x => toElement_ofScottContinuous g x

end DomainTheory.BridgeTheorems
