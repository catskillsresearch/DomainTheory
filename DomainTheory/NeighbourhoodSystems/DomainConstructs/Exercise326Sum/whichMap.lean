/-ai
The discriminator is the approximable map from the sum of two neighborhood systems to the truth domain that relates a sum neighborhood W to a truth neighborhood C precisely when the guard holds. It relates the two masters. On the right, the intersection of two truth values stays inside the guard by the zero-set and one-set intersection lemmas, or collapses to the master when both neighborhoods are the sum master. It is monotone because a smaller sum neighborhood is again a left copy, a right copy, or the master, while a larger truth neighborhood is the master or the same token, by the comparison lemmas for truth neighborhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_zero
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.Tmem_ge_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_zeroset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.inter_in_oneset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_left
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum.whichGuard_masterC

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **Exercise 3.26 (Scott 1981, PRG-19).** The discriminator `which : D₀ + D₁ → T`. -/
def whichMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty) :
    ApproximableMap (sum V₀ V₁ h₀ h₁) TD where
  rel W C := (sum V₀ V₁ h₀ h₁).mem W ∧ Example12.mem C ∧ whichGuard V₀ V₁ W C
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum V₀ V₁ h₀ h₁).master_mem, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  inter_right := by
    rintro W C C' ⟨hW, _, hg⟩ ⟨_, _, hg'⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · have hor := inter_in_zeroset hc (whichGuard_left hg' rfl (h₀ X hX))
      refine ⟨Or.inr (Or.inl ⟨X, hX, rfl⟩), ?_, Or.inl ⟨⟨X, hX, rfl⟩, hor⟩⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_zero
    · have hor := inter_in_oneset hc (whichGuard_right hg' rfl (h₁ Y hY))
      refine ⟨Or.inr (Or.inr ⟨Y, hY, rfl⟩), ?_, Or.inr (Or.inl ⟨⟨Y, hY, rfl⟩, hor⟩)⟩
      rcases hor with h | h
      · rw [h]; exact Example12.mem_master
      · rw [h]; exact Example12.mem_one
    · have hc' := whichGuard_masterC hg' rfl
      subst hc; subst hc'
      rw [Set.inter_self]
      exact ⟨Or.inl rfl, Example12.mem_master, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  mono := by
    rintro W W₂ C C₂ ⟨hW, hC, hg⟩ hW₂W hCC₂ hW₂ hC₂
    refine ⟨hW₂, hC₂, ?_⟩
    rcases hg with ⟨⟨X, hX, rfl⟩, hc⟩ | ⟨⟨Y, hY, rfl⟩, hc⟩ | ⟨rfl, hc⟩
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_inj₀ hW₂ hW₂W
      refine Or.inl ⟨⟨X₂, hX₂, rfl⟩, ?_⟩
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_zero hC₂ hCC₂)
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_inj₁ hW₂ hW₂W
      refine Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, ?_⟩)
      rcases hc with rfl | rfl
      · exact Or.inl (Tmem_ge_master hC₂ hCC₂)
      · exact Or.symm (Tmem_ge_one hC₂ hCC₂)
    · subst hc
      have hC₂m : C₂ = Example12.master := Tmem_ge_master hC₂ hCC₂
      rcases hW₂ with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩
      · exact Or.inr (Or.inr ⟨rfl, hC₂m⟩)
      · exact Or.inl ⟨⟨X₂, hX₂, rfl⟩, Or.inl hC₂m⟩
      · exact Or.inr (Or.inl ⟨⟨Y₂, hY₂, rfl⟩, Or.inl hC₂m⟩)

end DomainTheory.NeighbourhoodSystems.Exercise326
