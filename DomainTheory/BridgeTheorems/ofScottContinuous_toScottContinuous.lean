module
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.rel_iff_closure_le
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ofScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toScottContinuous
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.closure_le_element
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ext
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.subset_closure
public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_3_2
public import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology
public import DomainTheory.ContinuousLattice.FunctionSpaces.corollary_3_4
public import DomainTheory.ContinuousLattice.FunctionSpaces.scottLambda
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
