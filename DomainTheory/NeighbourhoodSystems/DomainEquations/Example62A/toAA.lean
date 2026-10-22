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
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_inter_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.embTuple_subset
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.memA_tuple_inv
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_mem
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Asys_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Apow
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apowNe
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.AAsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.apow_mem_prodN
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₀
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.aa_mem_inj₁

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB

variable {β : Type*} {n : ℕ}

variable {n : ℕ}

/-- **Forward half of `A ≅ Aⁿ + Aⁿ`.** An element `z` of `A` is sent to the sum element recording, for
each branch, whether `z` reaches the left copy `0X` (left summand `Aⁿ`) or the right copy `1Y` (right
summand `Aⁿ`). -/
def toAA (hn : 0 < n) (z : (Asys n hn).Element) : (AAsys hn).Element where
  mem W := W = sumMaster (Apow hn) (Apow hn)
    ∨ (∃ X, (∀ j, MemA n (X j)) ∧ W = inj₀ (prodN X) ∧ z.mem (embTuple false X))
    ∨ (∃ Y, (∀ j, MemA n (Y j)) ∧ W = inj₁ (prodN Y) ∧ z.mem (embTuple true Y))
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩ | ⟨Y, hY, rfl, -⟩)
    · exact (AAsys hn).master_mem
    · exact aa_mem_inj₀ hn hX
    · exact aa_mem_inj₁ hn hY
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩)
      (rfl | ⟨X', hX', rfl, hzX'⟩ | ⟨Y', hY', rfl, hzY'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl ⟨X', hX', by rw [sumMaster_inter_inj₀ (apow_mem_prodN hn hX')], hzX'⟩)
    · exact Or.inr (Or.inr ⟨Y', hY', by rw [sumMaster_inter_inj₁ (apow_mem_prodN hn hY')], hzY'⟩)
    · exact Or.inr (Or.inl ⟨X, hX,
        by rw [Set.inter_comm, sumMaster_inter_inj₀ (apow_mem_prodN hn hX)], hzX⟩)
    · refine Or.inr (Or.inl ⟨fun j => X j ∩ X' j, ?_, by rw [inj₀_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzX hzX'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzX hzX'; rwa [embTuple_inter] at hz
    · exfalso
      have hz := z.inter_mem hzX hzY'
      rw [embTuple_inter_ne (by decide : (false : Bool) ≠ true)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · exact Or.inr (Or.inr ⟨Y, hY,
        by rw [Set.inter_comm, sumMaster_inter_inj₁ (apow_mem_prodN hn hY)], hzY⟩)
    · exfalso
      have hz := z.inter_mem hzY hzX'
      rw [embTuple_inter_ne (by decide : (true : Bool) ≠ false)] at hz
      obtain ⟨t, ht⟩ := memA_nonempty hn (z.sub hz); exact Set.notMem_empty t ht
    · refine Or.inr (Or.inr ⟨fun j => Y j ∩ Y' j, ?_, by rw [inj₁_inter, prodN_inter], ?_⟩)
      · have hz := z.inter_mem hzY hzY'; rw [embTuple_inter] at hz
        exact memA_tuple_inv hn (z.sub hz)
      · have hz := z.inter_mem hzY hzY'; rwa [embTuple_inter] at hz
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hzX⟩ | ⟨Y, hY, rfl, hzY⟩) hW' hsub
    · exact Or.inl (eq_sumMaster_of_subset hW' hsub)
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨X', hX', rfl⟩ := hV'
        refine Or.inr (Or.inl ⟨X', hX', rfl, ?_⟩)
        exact z.up_mem hzX (MemA.tuple false hX')
          (embTuple_subset.mpr (prodN_subset.mp (inj₀_subset_inj₀.mp hsub)))
      · obtain ⟨b, hb⟩ := apowNe hn (prodN X) (apow_mem_prodN hn hX)
        exact absurd (hsub (il_mem_inj₀.mpr hb)) il_mem_inj₁
    · rcases hW' with rfl | ⟨V', hV', rfl⟩ | ⟨V', hV', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := apowNe hn (prodN Y) (apow_mem_prodN hn hY)
        exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · obtain ⟨Y', hY', rfl⟩ := hV'
        refine Or.inr (Or.inr ⟨Y', hY', rfl, ?_⟩)
        exact z.up_mem hzY (MemA.tuple true hY')
          (embTuple_subset.mpr (prodN_subset.mp (inj₁_subset_inj₁.mp hsub)))

end Example62A

end DomainTheory.NeighbourhoodSystems
