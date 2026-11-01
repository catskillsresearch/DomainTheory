module

public import DomainTheory.DataTypesAsLattices.Pomega.eBounds

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

instance (n k : ℕ) : Decidable (k ∈ e n) :=
  inferInstanceAs (Decidable (n.testBit k))

instance (n m : ℕ) : Decidable (e n ⊆ e m) :=
  decidable_of_iff (∀ k ≤ n, k ∈ e n → k ∈ e m) ⟨
    fun h k hk => h k (mem_e_le hk) hk,
    fun h _k _ hk => h hk⟩

end DomainTheory.DataTypesAsLattices
