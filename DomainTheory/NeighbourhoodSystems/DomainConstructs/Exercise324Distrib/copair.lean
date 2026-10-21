/-ai
The copairing of two approximable maps is the map out of the separated sum that relates a sum neighbourhood to an output neighbourhood when the output is the master, or the input is a left copy related by the first map, or the input is a right copy related by the second map. The master relates by the master output. For intersection, a master disjunct is absorbed by the other, two copies of the same side are identified by injectivity of that injection and passed to the corresponding map, and a left copy cannot equal a right copy because a nonempty left copy is not contained in a right copy. For monotonicity, a master output stays the master after the codomain shrinks, and a left or right copy shrinks to a smaller copy of the same side, to which the corresponding map's monotonicity applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** The *copairing* `[a, b] : 𝒟₀ + 𝒟₁ → 𝒟₂`: a left copy
`0X` is routed through `a`, a right copy `1Y` through `b`, and the basepoint `Λ` to `⊥` (so `Λ`
relates only to `Δ₂`). -/
def copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) V₂ where
  rel W Z := (sum V₀ V₁ h₀ h₁).mem W ∧ V₂.mem Z ∧
    (Z = V₂.master ∨
      (∃ X, W = inj₀ X ∧ a.rel X Z) ∨
      (∃ Y, W = inj₁ Y ∧ b.rel Y Z))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, V₂.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, _, hd⟩ ⟨_, _, hd'⟩
    have hmem : ∀ Z'' : Set γ,
        (Z'' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X Z'') ∨ (∃ Y, W = inj₁ Y ∧ b.rel Y Z'')) →
        V₂.mem Z'' := by
      rintro Z'' (rfl | ⟨_, _, hf⟩ | ⟨_, _, hg⟩)
      · exact V₂.master_mem
      · exact a.rel_cod hf
      · exact b.rel_cod hg
    have key : Z ∩ Z' = V₂.master ∨ (∃ X, W = inj₀ X ∧ a.rel X (Z ∩ Z')) ∨
        (∃ Y, W = inj₁ Y ∧ b.rel Y (Z ∩ Z')) := by
      rcases hd with rfl | ⟨X, hWX, hf⟩ | ⟨Y, hWY, hg⟩
      · rw [Set.inter_eq_right.mpr (V₂.sub_master (hmem _ hd'))]; exact hd'
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (a.rel_cod hf))]
          exact Or.inr (Or.inl ⟨X, hWX, hf⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX ▸ hWX')
          exact Or.inr (Or.inl ⟨X, hWX, a.inter_right hf hf'⟩)
        · exact absurd (hWX ▸ hWY' : (inj₀ X : Set _) = inj₁ Y')
            (fun h => not_inj₀_subset_inj₁ (h₀ X (a.rel_dom hf)) h.subset)
      · rcases hd' with rfl | ⟨X', hWX', hf'⟩ | ⟨Y', hWY', hg'⟩
        · rw [Set.inter_eq_left.mpr (V₂.sub_master (b.rel_cod hg))]
          exact Or.inr (Or.inr ⟨Y, hWY, hg⟩)
        · exact absurd (hWY ▸ hWX' : (inj₁ Y : Set _) = inj₀ X')
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (b.rel_dom hg)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY ▸ hWY')
          exact Or.inr (Or.inr ⟨Y, hWY, b.inter_right hg hg'⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ Z Z' ⟨_, _, hd⟩ hW₂W hZZ' hW₂ hZ'
    refine ⟨hW₂, hZ', ?_⟩
    rcases hd with rfl | ⟨X, rfl, hf⟩ | ⟨Y, rfl, hg⟩
    · left; exact Set.Subset.antisymm (V₂.sub_master hZ') hZZ'
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      exact Or.inr (Or.inl ⟨X₂, rfl, a.mono hf (inj₀_subset_inj₀.mp hW₂W) hZZ' hX₂ hZ'⟩)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      exact Or.inr (Or.inr ⟨Y₂, rfl, b.mono hg (inj₁_subset_inj₁.mp hW₂W) hZZ' hY₂ hZ'⟩)

end DomainTheory.NeighbourhoodSystems
