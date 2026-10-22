module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fstProj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inlInj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inlProj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictify
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.inclMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strctMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.twoPt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.unitPt
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.embF_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_proper
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.X_eq_master_of_nil_mem_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.subset_of_embF_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.X_eq_master_of_embT_subset_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.leftN_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplus_mem_leftN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictifyMap_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.incl_mono
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strct_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB
open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise627

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

theorem inlProj_comp_inlInj :
    (inlProj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlInj = idMap D₀ := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hX, _, hsub⟩, _, hZ, hsub'⟩
    exact ⟨hX, hZ, (leftN_subset_iff hX hZ).mp (hsub.trans hsub')⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨leftN D₀ D₁ X, ⟨hX, oplus_mem_leftN hX, subset_rfl⟩,
      oplus_mem_leftN hX, hZ, (leftN_subset_iff hX hZ).mpr hXZ⟩

theorem inlInj_comp_inlProj_le :
    (inlInj (D₀ := D₀) (D₁ := D₁) (h₀ := h₀) (h₁ := h₁)).comp inlProj
      ≤ idMap (oplusTok D₀ D₁ h₀ h₁) := by
  intro W W' hr
  obtain ⟨X, ⟨hW, _, hsub⟩, _, hW', hsub'⟩ := hr
  exact ⟨hW, hW', hsub.trans hsub'⟩

/-- **Exercise 6.27 (4).** `𝒟 ⊴ 𝒟 ⊕ ℰ`. (Uses `Classical.choice` via `oplus_mem_leftN`.) -/
theorem inl_trianglelefteq_oplus :
    D₀ ⊴ oplusTok D₀ D₁ h₀ h₁ :=
  trianglelefteq_of_projectionPair inlInj inlProj inlProj_comp_inlInj inlInj_comp_inlProj_le

end Exercise627
end DomainTheory.NeighbourhoodSystems
