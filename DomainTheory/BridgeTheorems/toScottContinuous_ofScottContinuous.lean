module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.ApproximableMapScott
public import DomainTheory.BridgeTheorems.scottContinuous_ext
import Mathlib.Tactic.Continuity.Init

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
