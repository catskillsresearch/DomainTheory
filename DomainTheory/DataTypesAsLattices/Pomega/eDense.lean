module

public import Mathlib.Order.SetNotation
public import DomainTheory.DataTypesAsLattices.Pomega.codeFinset
public import DomainTheory.DataTypesAsLattices.Pomega.ePrimrec

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace e

/-- Elements of $e_n$ when $e_n \subseteq x$ (empty if $e_n \not\subseteq x$). -/
def below (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ e n}

theorem singleton_eq (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (pow2 k).symm

theorem exists_mem {x : Pomega} {k : ℕ} (hk : k ∈ x) :
    ∃ n, e n ⊆ x ∧ k ∈ e n :=
  ⟨2 ^ k, by simp [pow2, Set.singleton_subset_iff, hk], by simp [pow2]⟩

theorem union_below_eq (x : Pomega) : (⋃ n, below x n) = x := by
  ext k
  constructor
  · intro hk
    obtain ⟨n, hn, hke⟩ := Set.mem_iUnion.mp hk
    exact hn hke
  · intro hk
    refine Set.mem_iUnion.mpr ⟨2 ^ k, ?_⟩
    simp [below, pow2, Set.singleton_subset_iff, hk]

end e

end DomainTheory.DataTypesAsLattices
