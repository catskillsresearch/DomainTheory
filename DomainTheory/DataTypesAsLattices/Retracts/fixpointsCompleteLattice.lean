module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove_ub
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove_le_of_ub
public import DomainTheory.DataTypesAsLattices.Retracts.lfpAbove_mem
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow_subset
public import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_1_complete
public import DomainTheory.DataTypesAsLattices.Retracts.gfpBelow_isGLB
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Retracts.vals_subset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

@[instance_reducible]
def fixpointsCompleteLattice {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    CompleteLattice (Fixpoints f) :=
  letI : SupSet (Fixpoints f) :=
    ⟨fun A => ⟨lfpAbove f (⋃₀ (Fixpoints.vals A)),
      lfpAbove_mem hf (Fixpoints.vals_subset A)⟩⟩
  { completeLatticeOfSup (Fixpoints f) (fun A => by
      refine ⟨?ub, ?least⟩
      · intro x hx
        change (x : Pomega) ⊆ lfpAbove f (⋃₀ (Fixpoints.vals A))
        exact lfpAbove_ub x.val ⟨x, hx, rfl⟩
      · intro z hz
        change lfpAbove f (⋃₀ (Fixpoints.vals A)) ⊆ z
        exact lfpAbove_le_of_ub hf z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)) with
    sInf := fun A => ⟨gfpBelow f (⋂₀ (Fixpoints.vals A)),
      theorem_4_1_complete f hf (Fixpoints.vals A) (Fixpoints.vals_subset A)⟩
    isGLB_sInf := fun A => by
      refine ⟨?lb, ?greatest⟩
      · intro x hx
        change gfpBelow f (⋂₀ (Fixpoints.vals A)) ⊆ x
        exact subset_trans (gfpBelow_subset f _)
          (Set.sInter_subset_of_mem ⟨x, hx, rfl⟩)
      · intro z hz
        change (z : Pomega) ⊆ gfpBelow f (⋂₀ (Fixpoints.vals A))
        exact gfpBelow_isGLB hf (Fixpoints.vals_subset A) z.property (fun y hy => by
          obtain ⟨w, hwA, rfl⟩ := hy
          exact hz hwA)
    bot := ⟨fix f, (theorem_1_4 hf).1⟩
    bot_le := fun x => (theorem_1_4 hf).2 x.val x.property }

end DomainTheory.DataTypesAsLattices
