module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem funEnt_union_step {w : Finset (FunToken A A)}
    {u u' v v' : Finset α}
    (hw : FunCon A A w) (hu : u ∈ A.Con) (hu' : u' ∈ A.Con)
    (hv : v ∈ A.Con) (hv' : v' ∈ A.Con)
    (hEnt : FunEnt A A w (mkFunToken A A u v hu hv))
    (hEnt' : FunEnt A A w (mkFunToken A A u' v' hu' hv'))
    (huU : u ∪' u' ∈ A.Con) :
    ∃ hvU : v ∪' v' ∈ A.Con,
      FunEnt A A w (mkFunToken A A (u ∪' u') (v ∪' v') huU hvU) := by
  obtain ⟨_, s1, hs1, hIn1, hOut1⟩ := hEnt
  obtain ⟨_, s2, hs2, hIn2, hOut2⟩ := hEnt'
  have hsub : s1 ∪' s2 ⊆ w := funion_subset_iff.mpr ⟨hs1, hs2⟩
  have hin : funInputUnion A A (s1 ∪' s2) ∈ A.Con := by
    rw [funInputUnion_funion]
    have hEntU : A.EntSet (u ∪' u')
        (funInputUnion A A s1 ∪' funInputUnion A A s2) :=
      proposition_2_3_vi A
        (proposition_2_3_v A hu huU (subset_funion_left _ _)
          (entSet_inputUnion_of_ent A A hIn1) (Finset.Subset.refl _))
        (proposition_2_3_v A hu' huU (subset_funion_right _ _)
          (entSet_inputUnion_of_ent A A hIn2) (Finset.Subset.refl _))
    exact A.con_subset (proposition_2_3_ii A huU hEntU) (subset_funion_right _ _)
  have hout : funOutputUnion A A s1 ∪' funOutputUnion A A s2 ∈ A.Con := by
    have := hw _ hsub hin
    rwa [funOutputUnion_funion] at this
  have hvU : v ∪' v' ∈ A.Con := by
    have hEntO : A.EntSet (funOutputUnion A A s1 ∪' funOutputUnion A A s2) (v ∪' v') :=
      proposition_2_3_vi A
        (proposition_2_3_v A
          (A.con_subset hout (subset_funion_left _ _)) hout
          (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
        (proposition_2_3_v A
          (A.con_subset hout (subset_funion_right _ _)) hout
          (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))
    exact A.con_subset (proposition_2_3_ii A hout hEntO) (subset_funion_right _ _)
  refine ⟨hvU, hw, s1 ∪' s2, hsub, ?_, ?_⟩
  · intro q hq
    rcases mem_funion.mp hq with hq | hq
    · exact proposition_2_3_v A hu huU (subset_funion_left _ _) (hIn1 q hq)
        (Finset.Subset.refl _)
    · exact proposition_2_3_v A hu' huU (subset_funion_right _ _) (hIn2 q hq)
        (Finset.Subset.refl _)
  · rw [funOutputUnion_funion]
    exact proposition_2_3_vi A
      (proposition_2_3_v A
        (A.con_subset hout (subset_funion_left _ _)) hout
        (subset_funion_left _ _) hOut1 (Finset.Subset.refl _))
      (proposition_2_3_v A
        (A.con_subset hout (subset_funion_right _ _)) hout
        (subset_funion_right _ _) hOut2 (Finset.Subset.refl _))

end InfoSys

end DomainTheory.InformationSystems
