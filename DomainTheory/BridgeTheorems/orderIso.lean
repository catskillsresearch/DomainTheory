/-ai
Along a pair of order isomorphisms, the Scott maps between two complete lattices are order-isomorphic to the Scott maps conjugated by those isomorphisms. The isomorphism wraps a Scott map as a conjugate and forgets the wrapping in the other direction. Both composites are the identity, and one conjugate lies below another exactly when the underlying Scott maps are so ordered.
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
public import DomainTheory.BridgeTheorems.conjScottMapFun_le_iff
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst19
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst21

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable {D E : Type*} [CompleteLattice D] [CompleteLattice E]

namespace ConjScottMap

variable {D' E' : Type*} [PartialOrder D'] [PartialOrder E']

variable (ιD : D ≃o D') (ιE : E ≃o E')

/-- **1972 ↔ round presentation:** Scott maps ≃ conjugates along the given isos. -/
noncomputable def orderIso : ScottMap D E ≃o ConjScottMap ιD ιE where
  toFun f := ⟨f⟩
  invFun g := g.scott
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro f g
    exact conjScottMapFun_le_iff ιD ιE

end ConjScottMap

end DomainTheory.BridgeTheorems
