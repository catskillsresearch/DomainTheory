/-ai
Passing an approximable map through toScottContinuous and then ofScottContinuous returns the original map.

By extensionality of approximable maps, a pair related by the composite has consistent domain and codomain and sends the closure of the domain into an element containing the closure of the codomain, which is the original relation by the closure criterion. Conversely, a related pair has consistent domain and codomain, and the same criterion puts every token of the codomain closure into the image element.
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

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element
@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem ofScottContinuous_toScottContinuous {A : InfoSys α} {B : InfoSys β}
    (f : ApproximableMap A B) :
    ofScottContinuous (toScottContinuous f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · intro ⟨hu, hv, hsub⟩
    exact (f.rel_iff_closure_le hu hv).2
      (B.closure_le_element (f.toElement (A.closure u hu)) hv hsub)
  · intro hrel
    refine ⟨f.rel_dom hrel, f.rel_cod hrel, ?_⟩
    intro y hy
    have hv : v ∈ B.Con := f.rel_cod hrel
    have hu : u ∈ A.Con := f.rel_dom hrel
    exact (f.rel_iff_closure_le hu hv).1 hrel (B.subset_closure hv (Finset.mem_coe.1 hy))

end DomainTheory.BridgeTheorems
