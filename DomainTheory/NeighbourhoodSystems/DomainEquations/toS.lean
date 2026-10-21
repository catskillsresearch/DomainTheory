/-ai
The forward half of the domain equation in Scott's Example 6.1 sends an element z of the sharp system of D to the element of the sum of D with the product of two sharp systems whose neighbourhoods are the master, the left copies of those neighbourhoods X of D for which the zero embedding of X lies in z, and the right copies of those product neighbourhoods of pairs for which the pair embedding lies in z.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_inter_embPair
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embZero_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.embPair_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Dsharp_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_embZero_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.memS_embPair_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.prod_dsharp_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.sumSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

section Equation

variable (D : NeighborhoodSystem α) (hD : ∀ X, D.mem X → X.Nonempty)

include hD

/-- **Example 6.1 — the forward half of the domain equation.** Sends an element `z` of `D^§` to an
element of `D + (D^§ × D^§)`, recording for each branch which `0X`/`1V` neighbourhoods `z` reaches:
`0X ∈ toS z ↔ embZero X ∈ z` and `1(P∪Q) ∈ toS z ↔ (1P∪2Q) ∈ z`. -/
def toS (z : (Dsharp D hD).Element) : (sumSys D hD).Element where
  mem W := W = sumMaster D (prod (Dsharp D hD) (Dsharp D hD))
    ∨ (∃ X, D.mem X ∧ W = inj₀ X ∧ z.mem (embZero X))
    ∨ (∃ P Q, MemS D P ∧ MemS D Q ∧ W = inj₁ (prodNbhd P Q) ∧ z.mem (embPair P Q))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨P, Q, hP, hQ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
    · exact Or.inr (Or.inr ⟨prodNbhd P Q, prod_mem_prodNbhd hP hQ, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨P', Q', hP', hQ', rfl, hzPQ'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ hX'], hzX'⟩)
    · exact Or.inr (Or.inr ⟨P', Q', hP', hQ',
        by rw [sumMaster_inter_inj₁ (prod_mem_prodNbhd hP' hQ')], hzPQ'⟩)
    · exact Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, sumMaster_inter_inj₀ hX], hzX⟩)
    · refine Or.inr (Or.inl ⟨X ∩ X', ?_, by rw [inj₀_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embZero_inter] at hz
        exact memS_embZero_inv hD (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embZero_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzPQ'; rw [embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨P, Q, hP, hQ,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (prod_mem_prodNbhd hP hQ)], hzPQ⟩)
    · exfalso
      have hz := z.inter_mem hzPQ hzX'; rw [Set.inter_comm, embZero_inter_embPair] at hz
      obtain ⟨t, ht⟩ := memS_nonempty hD (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨P ∩ P', Q ∩ Q', ?_, ?_, by rw [inj₁_inter, prodNbhd_inter], ?_⟩)
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).1
      · have hz := z.inter_mem hzPQ hzPQ'; rw [embPair_inter] at hz
        exact (memS_embPair_inv hD (z.sub hz)).2
      · have hz := z.inter_mem hzPQ hzPQ'; rwa [embPair_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨P, Q, hP, hQ, rfl, hzPQ⟩) hW' hsub
    · left
      exact eq_sumMaster_of_subset hW' hsub
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemS.zero hX') (embZero_subset.mpr (inj₀_subset_inj₀.mp hsub))
      · obtain ⟨a, ha⟩ := hD X hX
        exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := prod_dsharp_nonempty D hD (prodNbhd P Q) (prod_mem_prodNbhd hP hQ)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨P', Q', hP', hQ', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨P', Q', hP', hQ', rfl, ?_⟩)
        obtain ⟨hPP, hQQ⟩ := prodNbhd_subset_iff.mp (inj₁_subset_inj₁.mp hsub)
        exact z.up_mem hzPQ (MemS.pair hP' hQ') (embPair_subset.mpr ⟨hPP, hQQ⟩)

end Equation

end Example61

end DomainTheory.NeighbourhoodSystems
