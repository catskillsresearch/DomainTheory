module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510



section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)



variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}









variable {h₀ h₁}







variable (P₀ P₁)


/-- **`in₁` is computable.** Symmetric to `in₀`. -/
theorem osumInMap₁_isComputable :
    IsComputableMapS P₁.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₁ := by
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₁.X t.unpair.1 ⊆ P₁.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₁ (P₁.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₁.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X t.unpair.1)
      exact absurd (h (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
    · rcases h with ⟨h1, -⟩ | ⟨hn0, -⟩
      · rw [hL.1] at h1; exact absurd h1 (by decide)
      · exact absurd hL hn0
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, inj₁_subset_inj₁]
      exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
        fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.2)⟩
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₁_subset_sumMaster (P₁.mem_X _)⟩

end Coalesced
end DomainTheory.NeighbourhoodSystems
