/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise326
public import DomainTheory.Neighborhood.Exercise319Sum
public import DomainTheory.Neighborhood.Exercise326Sum.Basic
public import DomainTheory.Neighborhood.Exercise326Sum.not_sum_mem_empty

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise326

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap

variable {α β : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
















/-- On a "right" element, the round-trip `in₁ ∘ out₁` is the identity. -/
theorem inMap₁_outMap₁_eq_of_right {x : (sum V₀ V₁ h₀ h₁).Element}
    (hR : ∃ Y, V₁.mem Y ∧ x.mem (inj₁ Y)) :
    (inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap ((outMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap x) = x := by
  obtain ⟨Y₀, hY₀, hxY₀⟩ := hR
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨Y, ⟨W, hxW, _, _, hRWY⟩, _, hSZ, hinjYZ⟩
    have hxWY₀ : x.mem (W ∩ inj₁ Y₀) := x.inter_mem hxW hxY₀
    obtain ⟨Y₁, _, hY₁eq⟩ := mem_subset_inj₁ (x.sub hxWY₀) Set.inter_subset_right
    have hY₁Y : Y₁ ⊆ Y := by
      have : rightPart V₁ (W ∩ inj₁ Y₀) ⊆ Y :=
        (rightPart_mono V₁ Set.inter_subset_left).trans hRWY
      rwa [hY₁eq, rightPart_inj₁] at this
    have : (W ∩ inj₁ Y₀) ⊆ Z :=
      hY₁eq ▸ (inj₁_subset_inj₁.mpr hY₁Y).trans hinjYZ
    exact x.up_mem hxWY₀ hSZ this
  · intro hxZ
    rcases x.sub hxZ with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
    · exact ⟨V₁.master, ⟨sumMaster V₀ V₁, x.master_mem, (sum V₀ V₁ h₀ h₁).master_mem,
        V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩, V₁.master_mem,
        (sum V₀ V₁ h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
    · have := x.inter_mem hxY₀ hxZ
      rw [Set.inter_comm, inj₀_inter_inj₁] at this
      exact absurd (x.sub this) not_sum_mem_empty
    · exact ⟨Y', ⟨inj₁ Y', hxZ, Or.inr (Or.inr ⟨Y', hY', rfl⟩), hY', (rightPart_inj₁ V₁ Y').subset⟩,
        hY', Or.inr (Or.inr ⟨Y', hY', rfl⟩), subset_rfl⟩

end DomainTheory.Neighborhood.Exercise326
