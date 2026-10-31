module

public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9
public import DomainTheory.BridgeTheorems.ofScottContinuous_toScottContinuous
public import DomainTheory.BridgeTheorems.toScottContinuous_ofScottContinuous
public import DomainTheory.BridgeTheorems.InfoSysConstructions.instPartialOrderApproximableMap
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.le_iff_toElement_le
public import Mathlib.Algebra.Group.End
public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_2
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.corollary_3_4
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_5
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeRetractionProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_10_forward
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_10_converse
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_12
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_13
public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_unique
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_14
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.ConjScottMap

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

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
