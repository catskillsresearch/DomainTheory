/-ai
The indexed smash product of a family of neighbourhood systems over a nonempty index is the neighbourhood system on dependent pairs whose neighbourhoods are the product neighbourhood of the masters and the product neighbourhoods of finitely supported tuples that are non-master neighbourhoods at every index, and whose own master is the product neighbourhood of the masters.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_subset_iff
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.FinSupp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.inter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Exercise 6.29 — the indexed smash product `⊗_i D_i`.** The index type is non-empty so its
dependent-sum token set is non-empty. A proper neighbourhood is a cylinder proper in *every*
coordinate; closure under intersection is as for `iprod` plus the observation that
`X i ∩ X' i ⊆ X i ≠` master stays proper. -/
def iotimes [Nonempty ι] (D : ∀ i, NeighborhoodSystem (α i)) : NeighborhoodSystem (Σ i, α i) where
  mem W := W = iprodNbhd (fun i => (D i).master) ∨
    ∃ X : ∀ i, Set (α i), (∀ i, (D i).mem (X i)) ∧ (∀ i, X i ≠ (D i).master) ∧
      FinSupp D X ∧ W = iprodNbhd X
  master := iprodNbhd (fun i => (D i).master)
  master_nonempty := by
    cases ‹Nonempty ι› with
    | intro i =>
      obtain ⟨a, ha⟩ := (D i).master_nonempty
      exact ⟨⟨i, a⟩, ha⟩
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, _, _, rfl⟩)
    · exact subset_rfl
    · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i)
  inter_mem := by
    rintro W W' Z hW hW' hZ hsub
    rcases hW with rfl | ⟨X, hX, hXne, hXf, rfl⟩
    · have hW'sub : W' ⊆ iprodNbhd (fun i => (D i).master) := by
        rcases hW' with rfl | ⟨X', hX', _, _, rfl⟩
        · exact subset_rfl
        · exact iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX' i)
      rw [Set.inter_eq_right.mpr hW'sub]; exact hW'
    · rcases hW' with rfl | ⟨X', hX', hX'ne, hX'f, rfl⟩
      · rw [Set.inter_eq_left.mpr (iprodNbhd_subset_iff.mpr fun i => (D i).sub_master (hX i))]
        exact Or.inr ⟨X, hX, hXne, hXf, rfl⟩
      · rw [iprodNbhd_inter] at hsub ⊢
        obtain ⟨ZZ, hZZmem, rfl⟩ : ∃ ZZ, (∀ i, (D i).mem (ZZ i)) ∧ Z = iprodNbhd ZZ := by
          rcases hZ with rfl | ⟨ZZ, hZZ, _, _, rfl⟩
          · exact ⟨fun i => (D i).master, fun i => (D i).master_mem, rfl⟩
          · exact ⟨ZZ, hZZ, rfl⟩
        refine Or.inr ⟨fun i => X i ∩ X' i, fun i => ?_, fun i => ?_, ?_, rfl⟩
        · exact (D i).inter_mem (hX i) (hX' i) (hZZmem i) (iprodNbhd_subset_iff.mp hsub i)
        · intro heq
          exact hXne i (Set.Subset.antisymm ((D i).sub_master (hX i))
            (by rw [← heq]; exact Set.inter_subset_left))
        · exact hXf.inter hX'f

end Exercise629

end DomainTheory.NeighbourhoodSystems
