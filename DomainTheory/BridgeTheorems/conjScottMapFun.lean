/-ai
The conjugate of a Scott map along order isomorphisms of its domain and codomain is the original map, precomposed with the inverse isomorphism of the domain and postcomposed with the forward isomorphism of the codomain.
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
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9

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

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

/-- Conjugate a Scott map along order isomorphisms of the underlying lattices. -/
noncomputable def conjScottMapFun {D' E' : Type*} [LE D'] [LE E']
    (ιD : D ≃o D') (ιE : E ≃o E') (f : ScottMap D E) : D' → E' :=
  ⇑ιE ∘ (f : D → E) ∘ ⇑ιD.symm

end DomainTheory.BridgeTheorems
