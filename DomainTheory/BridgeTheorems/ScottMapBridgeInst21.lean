module

public import DomainTheory.BridgeTheorems.ConjScottMap
public import DomainTheory.BridgeTheorems.conjScottMapFun
public import DomainTheory.BridgeTheorems.ext
public import DomainTheory.BridgeTheorems.conjScottMapFun_le_iff
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
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst9
public import DomainTheory.BridgeTheorems.ScottMapBridgeInst19

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

noncomputable instance : PartialOrder (ConjScottMap ιD ιE) where
  le f g := ∀ x, conjScottMapFun ιD ιE f.scott x ≤ conjScottMapFun ιD ιE g.scott x
  le_refl _ _ := le_refl _
  le_trans _ _ _ hfg hgh x := le_trans (hfg x) (hgh x)
  le_antisymm f g hfg hgf := by
    refine ext ιD ιE ?_
    exact le_antisymm
      ((conjScottMapFun_le_iff ιD ιE).1 hfg)
      ((conjScottMapFun_le_iff ιD ιE).1 hgf)

end ConjScottMap

end DomainTheory.BridgeTheorems
