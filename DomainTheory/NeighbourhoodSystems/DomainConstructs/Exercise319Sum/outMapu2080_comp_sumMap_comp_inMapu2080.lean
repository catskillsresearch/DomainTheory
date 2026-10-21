/-ai
Composing the left injection, the sum of two approximable maps, and the left projection recovers the first map.

Two approximable maps agree when they relate the same pairs. If the composite relates X to Z, the intermediate output is the codomain master, a left copy related by the first map, or a right copy related by the second. The master case forces Z to be the codomain master, and monotonicity from the master relation of the first map gives the relation. The left-copy case gives an inclusion of the inputs and an inclusion of the output in Z, and monotonicity of the first map gives the relation. The right-copy case would place a nonempty left copy inside a right copy. Conversely, if the first map relates X to Z, the left copies of X and of Z witness the composite, because the left content of the left copy of Z is Z.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise318
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}










/-- **Exercise 3.19(iii) (Scott 1981, PRG-19).** `out₀ ∘ (f + g) ∘ in₀ = f`. -/
theorem outMap₀_comp_sumMap_comp_inMap₀ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₀ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₀ (h₀ := h₀) (h₁ := h₁))) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hX, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hleft⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · -- output master: leftPart = Δ₀', and Z ⊇ Δ₀' so Z = Δ₀'
      rw [leftPart_sumMaster] at hleft
      have : Z = V₀'.master := Set.Subset.antisymm (V₀'.sub_master hZ) hleft
      subst this
      exact f.mono f.master_rel (V₀.sub_master hX) subset_rfl hX V₀'.master_mem
    · -- output 0Y': X ⊆ X₀ and Y' ⊆ Z
      rw [leftPart_inj₀] at hleft
      have hXX₀ : X ⊆ X₀ := inj₀_subset_inj₀.mp (hWX₀ ▸ hinj)
      exact f.mono hf hXX₀ hleft hX hZ
    · -- impossible: in₀ forces 0X ⊆ W = 1Y₀
      exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY₀ ▸ hinj)).elim
  · intro hf
    refine ⟨inj₀ Z, ⟨inj₀ X, ⟨f.rel_dom hf, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, f.rel_cod hf, ?_⟩
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, f.rel_dom hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Z, rfl, rfl, hf⟩)
    · exact Or.inr (Or.inl ⟨Z, f.rel_cod hf, rfl⟩)
    · exact (leftPart_inj₀ V₀' Z).subset

end DomainTheory.NeighbourhoodSystems
