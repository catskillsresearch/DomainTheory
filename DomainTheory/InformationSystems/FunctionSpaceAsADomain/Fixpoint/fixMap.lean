
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_mono_w

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

namespace ApproximableMap

def fixMap : ApproximableMap (functionSystem A A) A where
  rel w v :=
    w ∈ (functionSystem A A).Con ∧ v ∈ A.Con ∧
      ∃ v0, FixReach A w v0 ∧ A.EntSet v0 v
  rel_dom h := h.1
  rel_cod h := h.2.1
  empty_rel :=
    ⟨(functionSystem A A).con_empty, A.con_empty, ∅, fixReach_empty A _, A.entSet_empty ∅⟩
  union_right := by
    rintro w v v' ⟨hw, hv, v0, hv0, hEnt0⟩ ⟨_, hv', v0', hv0', hEnt0'⟩
    have hv0C := fixReach_con A hv0
    have hv0'C := fixReach_con A hv0'
    have hUreach : FixReach A w (v0 ∪' v0') := fixReach_union A hw hv0 hv0'
    have hv0U := fixReach_con A hUreach
    have hEntU : A.EntSet (v0 ∪' v0') (v ∪' v') :=
      proposition_2_3_vi A
        (proposition_2_3_v A hv0C hv0U (subset_funion_left _ _) hEnt0 (Finset.Subset.refl _))
        (proposition_2_3_v A hv0'C hv0U (subset_funion_right _ _) hEnt0' (Finset.Subset.refl _))
    refine ⟨hw, ?_, v0 ∪' v0', hUreach, hEntU⟩
    exact A.con_subset (proposition_2_3_ii A hv0U hEntU) (subset_funion_right _ _)
  mono := by
    rintro w w' v v' ⟨hw, hv, v0, hv0, hEnt0⟩ hEntw hEntv hw' hv'
    refine ⟨hw', hv', v0, fixReach_mono_w A hw hw' hv0 hEntw, ?_⟩
    exact proposition_2_3_iv A (fixReach_con A hv0) hv hEnt0 hEntv

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
