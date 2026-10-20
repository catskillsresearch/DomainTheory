module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster_inter_embF
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTokMaster_inter_embT
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sumTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619.toSum_mem_inj₁

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The inverse half of the isomorphism, a token-level analogue of `Example62.fromBB`. -/
def fromSum (s : (sum D₀ D₁ h₀ h₁).Element) : (sumTok D₀ D₁ h₀ h₁).Element where
  mem W := W = sumTokMaster D₀ D₁
    ∨ (∃ X, D₀.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, D₁.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, hY, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumTokMaster_inter_embF hX'], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumTokMaster_inter_embT hY'], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumTokMaster_inter_embF hX], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, sumTokMaster_inter_embT hY], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm ((sumTok D₀ D₁ h₀ h₁).sub_master hW') hsub)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := h₀ X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := h₁ Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

end Exercise619

end DomainTheory.NeighbourhoodSystems
