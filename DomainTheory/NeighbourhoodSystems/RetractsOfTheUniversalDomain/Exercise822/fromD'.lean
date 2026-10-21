/-ai
The inverse from an element of D' to an element of C contains the cone of a string when the element contains the cone of that string's doubled encoding, and contains the singleton of a string when the element contains the cone of that string's completed encoding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_subsystem_B
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_enc_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_cone_enc_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.not_cone_enc_subset_cone_encC
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.cone_encC_subset_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **Inverse half of `C ≅ᴰ D'`.** -/
def fromD' (y : D'.Element) : C.Element where
  mem X := (∃ σ, y.mem (cone (enc σ)) ∧ X = cone σ) ∨ (∃ σ, y.mem (cone (encC σ)) ∧ X = ({σ} : Set Str))
  sub := by
    rintro X (⟨σ, -, rfl⟩ | ⟨σ, -, rfl⟩)
    · exact memC_cone σ
    · exact memC_singleton σ
  master_mem := by
    refine Or.inl ⟨[], ?_, cone_nil.symm⟩
    rw [enc_nil, cone_nil, ← D'_master]
    exact y.master_mem
  inter_mem := by
    rintro X X' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) (⟨τ, hτ, rfl⟩ | ⟨τ, hτ, rfl⟩)
    · -- cone/cone
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (enc σ) (enc τ) with h | h | h
      · exact Or.inl ⟨σ, hσ, by rw [Set.inter_eq_left.mpr (cone_subset_cone.mpr
          (cone_enc_subset_iff.mp h))]⟩
      · exact Or.inl ⟨τ, hτ, by rw [Set.inter_eq_right.mpr (cone_subset_cone.mpr
          (cone_enc_subset_iff.mp h))]⟩
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- cone/completion
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (enc σ) (encC τ) with h | h | h
      · exfalso
        exact absurd h not_cone_enc_subset_cone_encC
      · exact Or.inr ⟨τ, hτ, by rw [Set.inter_eq_right.mpr (singleton_subset_cone.mpr
          (cone_encC_subset_cone_enc_iff.mp h))]⟩
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- completion/cone
      have hy := y.inter_mem hσ hτ
      rcases cone_trichotomy (encC σ) (enc τ) with h | h | h
      · exact Or.inr ⟨σ, hσ, by rw [Set.inter_eq_left.mpr (singleton_subset_cone.mpr
          (cone_encC_subset_cone_enc_iff.mp h))]⟩
      · exfalso
        exact absurd h not_cone_enc_subset_cone_encC
      · rw [h] at hy; exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
    · -- completion/completion
      have hy := y.inter_mem hσ hτ
      by_cases hστ : σ = τ
      · subst hστ
        exact Or.inr ⟨σ, hσ, by rw [Set.inter_self]⟩
      · exfalso
        have h' : cone (encC σ) ∩ cone (encC τ) = ∅ := by
          rcases cone_trichotomy (encC σ) (encC τ) with h | h | h
          · exact absurd (cone_encC_subset_iff.mp h) hστ
          · exact absurd (cone_encC_subset_iff.mp h) (Ne.symm hστ)
          · exact h
        rw [h'] at hy
        exact absurd (B_nonempty ∅ (D'_subsystem_B.sub (y.sub hy))) (by simp)
  up_mem := by
    rintro X X' (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩) hX' hsub
    · rcases hX' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := cone_subset_cone.mp hsub
        exact y.up_mem hσ (Or.inl ⟨κ, rfl⟩) (cone_enc_subset_iff.mpr hκσ)
      · exfalso
        have h1 : σ ∈ cone σ := List.prefix_rfl
        have h2 : σ ++ [true] ∈ cone σ := ⟨[true], rfl⟩
        have hσκ1 : σ = κ := hsub h1
        have hσκ2 : σ ++ [true] = κ := hsub h2
        exact absurd (hσκ2.trans hσκ1.symm) (by simp)
    · rcases hX' with ⟨κ, rfl⟩ | ⟨κ, rfl⟩
      · refine Or.inl ⟨κ, ?_, rfl⟩
        have hκσ : κ <+: σ := singleton_subset_cone.mp hsub
        exact y.up_mem hσ (Or.inl ⟨κ, rfl⟩) (cone_encC_subset_cone_enc_iff.mpr hκσ)
      · refine Or.inr ⟨κ, ?_, rfl⟩
        have hσκ : σ = κ := hsub rfl
        exact y.up_mem hσ (Or.inr ⟨κ, rfl⟩) (cone_encC_subset_iff.mpr hσκ)

end Exercise822

end DomainTheory.NeighbourhoodSystems
