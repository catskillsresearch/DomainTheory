/-ai
The forward map from an element of C to an element of D' contains the cone of a doubled encoding when the element contains the cone of the original string, and contains the cone of a completed encoding when the element contains the singleton of the original string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.C_nonempty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_enc_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_cone_enc_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.not_cone_enc_subset_cone_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **Forward half of `C ≅ᴰ D'`.** Sends a `C`-element `x` to the `D'`-element recording, for each
`D'`-shape, whether `x` reaches the corresponding `C`-neighbourhood. -/
def toD' (x : C.Element) : D'.Element where
  mem W := (∃ σ, x.mem (cone σ) ∧ W = cone (enc σ)) ∨ (∃ σ, x.mem ({σ} : Set Str) ∧ W = cone (encC σ))
  sub := by
    rintro W (⟨σ, -, rfl⟩ | ⟨σ, -, rfl⟩)
    · exact Or.inl ⟨σ, rfl⟩
    · exact Or.inr ⟨σ, rfl⟩
  master_mem := by
    rw [D'_master]
    refine Or.inl ⟨[], ?_, ?_⟩
    · rw [cone_nil]; exact x.master_mem
    · rw [enc_nil, cone_nil]
  inter_mem := by
    rintro W W' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · -- cone/cone
      have hx := x.inter_mem hσ hτ
      rcases cone_trichotomy σ τ with h | h | h
      · exact Or.inl ⟨σ, hσ, by rw [Set.inter_eq_left.mpr
          (cone_enc_subset_iff.mpr (cone_subset_cone.mp h))]⟩
      · exact Or.inl ⟨τ, hτ, by rw [Set.inter_eq_right.mpr
          (cone_enc_subset_iff.mpr (cone_subset_cone.mp h))]⟩
      · rw [h] at hx; exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- cone/singleton
      have hx := x.inter_mem hσ hτ
      rcases singleton_cone_nd σ τ with h | h | h
      · exact Or.inr ⟨τ, hτ, by rw [Set.inter_eq_right.mpr
          (cone_encC_subset_cone_enc_iff.mpr (singleton_subset_cone.mp h))]⟩
      · exfalso
        have h1 : σ ∈ cone σ := List.prefix_rfl
        have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
        have hστ1 : σ = τ := h h1
        have hστ2 : σ ++ [true] = τ := h h2
        exact absurd (hστ2.trans hστ1.symm) (by simp)
      · exfalso
        have h' : cone σ ∩ {τ} = ∅ := by rw [Set.inter_comm]; exact h
        rw [h'] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- singleton/cone
      have hx := x.inter_mem hσ hτ
      rcases singleton_cone_nd τ σ with h | h | h
      · exact Or.inr ⟨σ, hσ, by rw [Set.inter_eq_left.mpr
          (cone_encC_subset_cone_enc_iff.mpr (singleton_subset_cone.mp h))]⟩
      · exfalso
        have h1 : τ ∈ cone τ := List.prefix_rfl
        have h2 : τ ++ [true] ∈ cone τ := ⟨[true], rfl⟩
        have hτσ1 : τ = σ := h h1
        have hτσ2 : τ ++ [true] = σ := h h2
        exact absurd (hτσ2.trans hτσ1.symm) (by simp)
      · exfalso
        rw [h] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
    · -- singleton/singleton
      have hx := x.inter_mem hσ hτ
      by_cases hστ : σ = τ
      · subst hστ
        exact Or.inr ⟨σ, hσ, by rw [Set.inter_self]⟩
      · exfalso
        have h' : ({σ} : Set Str) ∩ {τ} = ∅ := by
          ext w; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro rfl; exact hστ
        rw [h'] at hx
        exact absurd (C_nonempty ∅ (x.sub hx)) (by simp)
  up_mem := by
    rintro W W' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) hW' hsub
    · rcases hW' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_enc_subset_iff.mp hsub
        exact x.up_mem hσ (memC_cone κ) (cone_subset_cone.mpr hκσ)
      · exact absurd hsub not_cone_enc_subset_cone_encC
    · rcases hW' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_encC_subset_cone_enc_iff.mp hsub
        exact x.up_mem hσ (memC_cone κ) (singleton_subset_cone.mpr hκσ)
      · refine Or.inr ⟨κ, ?_, rfl⟩
        have hστ : σ = κ := cone_encC_subset_iff.mp hsub
        exact hστ ▸ hσ

end Exercise822

end DomainTheory.NeighbourhoodSystems
