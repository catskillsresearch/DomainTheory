/-ai
The inverse half of A ≅ Aⁿ + Aⁿ sends an element s of the separated sum to the element of A that contains the set of all strings, contains a false-tagged tuple of X precisely when s contains the left injection of the proper product of X, and contains a true-tagged tuple of Y precisely when s contains the right injection of the proper product of Y.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.MemA
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.prodN_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.npow_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.mem_embTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.tag_eq_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.toAA_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- **Inverse half of `A ≅ Aⁿ + Aⁿ`.** -/
def fromAA (hn : 0 < n) (s : (AAsys hn).Element) : (Asys n hn).Element where
  mem W := W = Set.univ
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = embTuple false X ∧ s.mem (inj₀ (prodN X)))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = embTuple true Y ∧ s.mem (inj₁ (prodN Y)))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact MemA.univ
    · exact MemA.tuple false hX
    · exact MemA.tuple true hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩)
      (rfl | ⟨X', hX', rfl, hsX'⟩ | ⟨Y', hY', rfl, hsY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [Set.univ_inter], hsX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [Set.univ_inter], hsY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_univ], hsX⟩)
    · have hs := s.inter_mem hsX hsX'
      rw [inj₀_inter, prodN_inter] at hs
      exact Or.inr (Or.inl ⟨fun j => X j ∩ X' j,
        apow_mem_prodN_inv hn (aa_mem_inj₀_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
    · exfalso
      have hs := s.inter_mem hsX hsY'; rw [inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_univ], hsY⟩)
    · exfalso
      have hs := s.inter_mem hsY hsX'; rw [Set.inter_comm, inj₀_inter_inj₁] at hs
      obtain ⟨t, ht⟩ := aa_mem_nonempty hn (s.sub hs); exact Set.notMem_empty t ht
    · have hs := s.inter_mem hsY hsY'
      rw [inj₁_inter, prodN_inter] at hs
      exact Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j,
        apow_mem_prodN_inv hn (aa_mem_inj₁_inv hn (s.sub hs)), by rw [embTuple_inter], hs⟩)
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hsX⟩ | ⟨Y, hY, rfl, hsY⟩) hW' hsub
    · exact Or.inl (Set.univ_subset_iff.mp hsub)
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : false = i'' := tag_eq_of_subset hn hX hsub
        subst htag
        refine Or.inr (Or.inl ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsX (aa_mem_inj₀ hn hV)
          (inj₀_subset_inj₀.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))
    · cases hW' with
      | univ => exact Or.inl rfl
      | @tuple i'' V hV =>
        have htag : true = i'' := tag_eq_of_subset hn hY hsub
        subst htag
        refine Or.inr (Or.inr ⟨V, hV, rfl, ?_⟩)
        exact s.up_mem hsY (aa_mem_inj₁ hn hV)
          (inj₁_subset_inj₁.mpr (prodN_subset.mpr (embTuple_subset.mp hsub)))

end Example62A

end DomainTheory.NeighbourhoodSystems
