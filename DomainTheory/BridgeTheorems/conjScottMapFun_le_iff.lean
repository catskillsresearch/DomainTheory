/-ai
Conjugated Scott maps are pointwise ordered if and only if the underlying Scott maps are ordered.

If the conjugates are pointwise ordered, the inequality at the image of an element rewrites, after cancelling the domain isomorphism with its inverse, as an inequality of the codomain isomorphism applied to the two maps, and the codomain isomorphism reflects the order. Conversely, an inequality of Scott maps transports along the monotone codomain isomorphism after the argument is pulled back by the inverse domain isomorphism.
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
public import DomainTheory.BridgeTheorems.conjScottMapFun

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

theorem conjScottMapFun_le_iff {D' E' : Type*} [PartialOrder D'] [PartialOrder E']
    (ιD : D ≃o D') (ιE : E ≃o E') {f g : ScottMap D E} :
    (∀ x : D', conjScottMapFun ιD ιE f x ≤ conjScottMapFun ιD ιE g x) ↔ f ≤ g := by
  constructor
  · intro h
    rw [ScottMap.le_def]
    intro x
    have hx : ιE (f x) ≤ ιE (g x) := by
      simpa [conjScottMapFun, OrderIso.symm_apply_apply] using h (ιD x)
    exact ιE.map_rel_iff.mp hx
  · intro hfg x
    exact ιE.monotone (hfg (ιD.symm x))

end DomainTheory.BridgeTheorems
