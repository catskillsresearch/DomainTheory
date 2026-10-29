module

public import DomainTheory.BridgeTheorems.conjScottMapFun
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_2
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSupMaps_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_finset_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.pointwiseSubbasic_scottOpen
public import DomainTheory.ContinuousLattice.FunctionSpaces.wayBelow_le_finset_sup_step
public import DomainTheory.ContinuousLattice.FunctionSpaces.corollary_3_4
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_5
public import DomainTheory.ContinuousLattice.FunctionSpaces.retr_ambientSSup_eq_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.retr_wayBelow_of_wayBelow_incl
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_retr_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.image_retr_wayBelow_nonempty
public import DomainTheory.ContinuousLattice.FunctionSpaces.image_retr_wayBelow_directed
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_injective
public import DomainTheory.ContinuousLattice.FunctionSpaces.retr_bot
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_bot
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_finset_sup
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_10_forward
public import DomainTheory.ContinuousLattice.FunctionSpaces.retr_eq_sSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_10_converse
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_le_of_mem
public import DomainTheory.ContinuousLattice.FunctionSpaces.sInf_image_le_sInf_image_of_subset
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_eq_of_comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend_maximal
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend_mono
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_eq_of_ext
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtend_eq_of_ext
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_retr
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_incl
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottSubspaceExtendInf_mono_incl_apply
public import DomainTheory.ContinuousLattice.FunctionSpaces.lemma_3_9_incl_inf
public import DomainTheory.ContinuousLattice.FunctionSpaces.lemma_3_9_retr_inf
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
