module

public import Mathlib.Order.SetNotation
public import DomainTheory.DataTypesAsLattices.Pomega.codeFinset
public import DomainTheory.DataTypesAsLattices.Pomega.ePrimrec

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def eBelow (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ e n}

theorem singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e.pow2 k).symm

theorem exists_e_mem {x : Pomega} {k : ℕ} (hk : k ∈ x) :
    ∃ n, e n ⊆ x ∧ k ∈ e n :=
  ⟨2 ^ k, by simp [e.pow2, Set.singleton_subset_iff, hk], by simp [e.pow2]⟩

theorem union_e_eq (x : Pomega) : (⋃ n, eBelow x n) = x := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hke⟩ := Set.mem_iUnion.mp hk
    exact hn hke
  · intro hk
    refine Set.mem_iUnion.mpr ⟨2 ^ k, ?_⟩
    simp [eBelow, e.pow2, Set.singleton_subset_iff, hk]

end DomainTheory.DataTypesAsLattices
