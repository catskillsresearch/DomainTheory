/-ai
This instance orders the Scott-continuous maps between the domains of two information systems by the pointwise order of their underlying functions. Reflexivity and transitivity are the corresponding properties of that pointwise order. Antisymmetry combines the two pointwise inequalities at each element and applies extensionality of Scott-continuous maps.
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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Pointwise order on Scott-continuous maps of InfoSys domains. -/
instance instPartialOrderScottContinuous (A : InfoSys α) (B : InfoSys β) :
    PartialOrder (ScottContinuous A B) where
  le f g := ∀ x, f.toFun x ≤ g.toFun x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm _ _ hfg hgf :=
    scottContinuous_ext fun x => le_antisymm (hfg x) (hgf x)

end DomainTheory.BridgeTheorems
