module
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.ScottContinuous
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

instance instPartialOrderScottContinuous (A : InfoSys α) (B : InfoSys β) :
    PartialOrder (ScottContinuous A B) where
  le f g := ∀ x, f.toFun x ≤ g.toFun x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf :=
    scottContinuous_ext fun x => le_antisymm (hfg x) (hgf x)

end DomainTheory.BridgeTheorems
