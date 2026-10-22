module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.isStrict_constBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.StrictMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_inter_right
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_subset
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_mem_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_mem_of_mem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.toStrictMap_rel
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_toStrictFilter
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_prodNbhd_form

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Strict uncurry combinator.** `uncurry⊥ : (𝒟₀ →⊥ (𝒟₁ →⊥ 𝒟₂)) → ((𝒟₀ ⊗ 𝒟₁) →⊥ 𝒟₂)`,
`X ∪ Y (uncurry⊥ h) Z ↔ X h [Y, Z]`. -/
def smashUncurryMap (h : StrictMap V₀ (strictFun V₁ V₂)) : StrictMap (smash V₀ V₁) V₂ :=
  ⟨{ rel := fun W Z => (smash V₀ V₁).mem W ∧ h.1.rel (Sum.inl ⁻¹' W) (sstep (Sum.inr ⁻¹' W) Z)
     rel_dom := fun hh => hh.1
     rel_cod := by
       rintro W Z ⟨_, hrel⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       exact f.1.rel_cod hf
     master_rel := by
       refine ⟨(smash V₀ V₁).master_mem, ?_⟩
       rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
         inl_preimage_prodNbhd, inr_preimage_prodNbhd, sstep_master_eq]
       exact h.1.master_rel
     inter_right := by
       rintro W Z Z' ⟨hW, hrel⟩ ⟨_, hrel'⟩
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       obtain ⟨f', hf'⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel')).2
       refine ⟨hW, ?_⟩
       rw [← sstep_inter_right (f.1.rel_cod hf) (f'.1.rel_cod hf')]
       exact h.1.inter_right hrel hrel'
     mono := by
       rintro W W₂ Z Z' ⟨_, hrel⟩ hW₂W hZZ' hW₂ hZ'
       have hinl : Sum.inl ⁻¹' W₂ ⊆ Sum.inl ⁻¹' W := Set.preimage_mono hW₂W
       have hinr : Sum.inr ⁻¹' W₂ ⊆ Sum.inr ⁻¹' W := Set.preimage_mono hW₂W
       obtain ⟨A, B, hA, hB, rfl⟩ := smash_mem_prodNbhd_form hW₂
       refine ⟨hW₂, ?_⟩
       rw [inl_preimage_prodNbhd] at hinl
       rw [inr_preimage_prodNbhd] at hinr
       rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
       obtain ⟨f, hf⟩ := (strictFun_mem_iff.mp (h.1.rel_cod hrel)).2
       have hfB : f.1.rel B Z' := f.1.mono hf hinr hZZ' hB hZ'
       exact h.1.mono hrel hinl (sstep_subset hB hZ' hinr hZZ') hA
         (sstep_mem_of_mem (g := f) hfB) },
   by
     rintro Z ⟨_, hrel⟩
     rw [show (smash V₀ V₁).master = prodNbhd V₀.master V₁.master from rfl,
       inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel
     have huniv : sstep V₁.master Z = (Set.univ : Set (StrictMap V₁ V₂)) := h.2 hrel
     have hcb : (⟨constMap V₁ V₂.bot, isStrict_constBot⟩ : StrictMap V₁ V₂) ∈ sstep V₁.master Z := by
       rw [huniv]; exact Set.mem_univ _
     obtain ⟨_, hZ⟩ := hcb
     rwa [NeighborhoodSystem.mem_bot] at hZ⟩

end DomainTheory.NeighbourhoodSystems.Exercise510
