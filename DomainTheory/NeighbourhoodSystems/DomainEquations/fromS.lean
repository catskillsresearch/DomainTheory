module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61.MemS
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embZero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embL
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embR
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.mem_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset_Gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_subset_gamma
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.toS_mem_inj₁

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- **Example 6.1 — the inverse half of the domain equation.** Sends an element `s` of
`D + (D^§ × D^§)` back to an element of `D^§`. -/
def fromS (s : (sumSys D hD).Element) : (Dsharp D hD).Element where
  mem W := W = Gamma D
    ∨ (∃ X, D.mem X ∧ W = embZero X ∧ s.mem (inj₀ X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = embPair P Q ∧ s.mem (inj₁ (prodNbhd P Q)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact MemS.gamma
    · exact MemS.zero hX
    · exact MemS.pair hP hQ
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨P', Q', hP', hQ', rfl, hsPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX',
        by rw [Set.inter_eq_right.mpr (embZero_subset_Gamma hX')], hsX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [Set.inter_eq_right.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP') (memS_subset_gamma hQ'))], hsPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_eq_left.mpr (embZero_subset_Gamma hX)], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embZero_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv D hD (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsPQ'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_eq_left.mpr
          (embPair_subset_Gamma (memS_subset_gamma hP) (memS_subset_gamma hQ))], hsPQ⟩)
    · exfalso
      have hs := s.inter_mem hsPQ hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sumSys_mem_nonempty D hD (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [embPair_inter], ?_⟩)
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).1
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs
        exact (prod_mem_prodNbhd_iff.mp (sum_mem_inj₁_inv D hD (s.sub hs))).2
      · have hs := s.inter_mem hsPQ hsPQ'; rw [inj₁_inter, prodNbhd_inter] at hs; exact hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨P, Q, hP, hQ, rfl, hsPQ⟩) hW' hsub
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hW') hsub)
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embZero_subset.mp hsub))
      | @pair P' Q' hP' hQ' =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        have hmem : (([], a) : List Bool × α) ∈ embPair P' Q' := hsub ⟨rfl, ha⟩
        rcases hmem with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
    · cases hW' with
      | gamma => exact Or.inl rfl
      | @zero X' hX' =>
        exfalso
        obtain ⟨t, ht⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
        have hcons : t.1 ≠ [] := by
          rcases ht with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
          · simp [hp']
          · simp [hq']
        have hz : t ∈ embZero X' := hsub ht
        exact hcons hz.1
      | @pair P' Q' hP' hQ' =>
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := embPair_subset.mp hsub
        exact s.up_mem hsPQ (Or.inr (Or.inr ⟨prodNbhd P' Q', prod_mem_prodNbhd hP' hQ', rfl⟩))
          (inj₁_subset_inj₁.mpr (prodNbhd_subset_iff.mpr ⟨hPP, hQQ⟩))

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
