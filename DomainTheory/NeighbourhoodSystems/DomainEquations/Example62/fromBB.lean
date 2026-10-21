/-ai
The map back from an element of the sum of the binary-sequence domain with itself sends a sum element to the element whose neighbourhoods are the master, the false-bit taggings of those neighbourhoods whose left injection belongs to the sum element, and the true-bit taggings of those neighbourhoods whose right injection belongs to the sum element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.memB_cases
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.sum_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.toBB_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 — inverse half of `B ≅ B + B`.** -/
def fromBB (s : BB.Element) : B.Element where
  mem W := W = Set.univ
    ∨ (∃ X, B.mem X ∧ W = embBit false X ∧ s.mem (inj₀ X))
    ∨ (∃ Y, B.mem Y ∧ W = embBit true Y ∧ s.mem (inj₁ Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact ⟨[], cone_nil.symm⟩
    · exact memB_embBit false hX
    · exact memB_embBit true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsX hsX'; rw [inj₀_inter] at hs
        exact sum_mem_inj₀_inv (s.sub hs)
      · have hs := s.inter_mem hsX hsX'; rwa [inj₀_inter] at hs
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := sum_mem_nonempty (s.sub hs); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨Y ∩ Y', ?_, by rw [embBit_inter], ?_⟩)
      · have hs := s.inter_mem hsY hsY'; rw [inj₁_inter] at hs
        exact sum_mem_inj₁_inv (s.sub hs)
      · have hs := s.inter_mem hsY hsY'; rwa [inj₁_inter] at hs
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact s.up_mem hsX (Or.inr (Or.inl ⟨X', hX', rfl⟩))
          (inj₀_subset_inj₀.mpr (embBit_subset.mp hsub))
      · exfalso
        obtain ⟨a, ha⟩ := B_nonempty X hX
        obtain ⟨w', he, -⟩ := hsub (⟨a, rfl, ha⟩ : (false :: a) ∈ embBit false X)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
    · rcases memB_cases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩
      · exact Or.inl rfl
      · exfalso
        obtain ⟨b, hb⟩ := B_nonempty Y hY
        obtain ⟨w', he, -⟩ := hsub (⟨b, rfl, hb⟩ : (true :: b) ∈ embBit true Y)
        rw [List.cons.injEq] at he; exact absurd he.1 (by decide)
      · refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact s.up_mem hsY (Or.inr (Or.inr ⟨Y', hY', rfl⟩))
          (inj₁_subset_inj₁.mpr (embBit_subset.mp hsub))

end Example62

end DomainTheory.NeighbourhoodSystems
