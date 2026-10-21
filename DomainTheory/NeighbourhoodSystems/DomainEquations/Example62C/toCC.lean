/-ai
The forward half of the isomorphism C ≅ 𝟙 + C + C sends an element x of C to the element of the three-way sum whose neighbourhoods are the master, the left copy of the unit universe when x contains the singleton of the empty word, a middle copy of a neighbourhood X of C when x contains the false embedding of X, or a right copy of a neighbourhood Y of C when x contains the true embedding of Y. Each of these four forms is a neighbourhood of the sum, and the master is included. The intersection of two such forms is again one of them: a master meets a copy in that copy, two unit copies meet in the unit copy, and two embeddings of the same bit meet in the embedding of the intersection, with the element's own intersection rewritten by the embedding-intersection law supplying both the neighbourhood and the membership; a unit singleton against an embedding, or two embeddings of opposite bits, rewrites to an empty intersection, which cannot contain a point of a nonempty subneighbourhood of x. An upper neighbourhood of one of these forms is again one of them: above the master the equality-of-master lemma applies, above a unit copy a change to a middle or right copy cannot contain the unit token, and above a bit copy a change to the other tags cannot contain a token of the original bit, while a larger copy of the same bit is reached by upward closure of x along the embedding.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t2_not_mem_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t0_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.t1_not_mem_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j0_inter_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_inter_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j1_subset_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.j2_subset_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.none_mem_master3
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j0
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j1
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.master3_inter_j2
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.eq_master3_of_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.C_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.memC_embBit_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.singleton_nil_inter_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C.CC

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

variable {α β γ : Type*}

variable (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ)

variable {V₀ V₁ V₂}

namespace Example62C

/-- **Example 6.2 — forward half of `C ≅ 𝟙 + C + C`.** -/
def toCC (x : C.Element) : CC.Element where
  mem W := W = master3 unitSys C C
    ∨ (W = j0 (Set.univ : Set Unit) ∧ x.mem ({[]} : Set Str))
    ∨ (∃ X, C.mem X ∧ W = j1 X ∧ x.mem (embBit false X))
    ∨ (∃ Y, C.mem Y ∧ W = j2 Y ∧ x.mem (embBit true Y))
  sub := by
    rintro W (rfl | ⟨rfl, -⟩ | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨Set.univ, rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩)
      (rfl | ⟨rfl, hzU'⟩ | ⟨X', hX', rfl, hzF'⟩ | ⟨Y', hY', rfl, hzT'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨master3_inter_j0 rfl, hzU'⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨X', hX', master3_inter_j1 hX', hzF'⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨Y', hY', master3_inter_j2 hY', hzT'⟩))
    · exact Or.inr (Or.inl ⟨by rw [Set.inter_comm, master3_inter_j0 rfl], hzU⟩)
    · refine Or.inr (Or.inl ⟨?_, hzU⟩)
      rw [j0_inter_j0, Set.inter_self]
    · exfalso
      have hx := x.inter_mem hzU hzF'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzU hzT'
      rw [singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inl ⟨X, hX, by rw [Set.inter_comm, master3_inter_j1 hX], hzF⟩))
    · exfalso
      have hx := x.inter_mem hzF hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inl ⟨X ∩ X', ?_, j1_inter_j1 X X', ?_⟩))
      · have hx := x.inter_mem hzF hzF'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzF hzF'; rwa [embBit_inter] at hx
    · exfalso
      have hx := x.inter_mem hzF hzT'
      rw [embBit_inter_ne (show (false : Bool) ≠ true by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j2 hY], hzT⟩))
    · exfalso
      have hx := x.inter_mem hzT hzU'
      rw [Set.inter_comm, singleton_nil_inter_embBit] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · exfalso
      have hx := x.inter_mem hzT hzF'
      rw [embBit_inter_ne (show (true : Bool) ≠ false by decide)] at hx
      obtain ⟨t, ht⟩ := C_nonempty _ (x.sub hx); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr (Or.inr ⟨Y ∩ Y', ?_, j2_inter_j2 Y Y', ?_⟩))
      · have hx := x.inter_mem hzT hzT'; rw [embBit_inter] at hx; exact memC_embBit_inv (x.sub hx)
      · have hx := x.inter_mem hzT hzT'; rwa [embBit_inter] at hx
  up_mem := by
    rintro W W' (rfl | ⟨rfl, hzU⟩ | ⟨X, hX, rfl, hzF⟩ | ⟨Y, hY, rfl, hzT⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub (CC.sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain rfl := hX'; exact Or.inr (Or.inl ⟨rfl, hzU⟩)
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j1
      · exact absurd (hsub (t0_mem_j0.mpr (Set.mem_univ ()))) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · refine Or.inr (Or.inr (Or.inl ⟨Y', hY', rfl, ?_⟩))
        exact x.up_mem hzF (memC_embBit false hY') (embBit_subset.mpr (j1_subset_j1.mp hsub))
      · obtain ⟨b, hb⟩ := C_nonempty X hX
        exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := C_nonempty Y hY
        exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · refine Or.inr (Or.inr (Or.inr ⟨Z', hZ', rfl, ?_⟩))
        exact x.up_mem hzT (memC_embBit true hZ') (embBit_subset.mpr (j2_subset_j2.mp hsub))

end Example62C

end DomainTheory.NeighbourhoodSystems
