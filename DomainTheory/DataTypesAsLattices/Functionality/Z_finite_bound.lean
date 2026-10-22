module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Z_finite_bound (p q m : ℕ) :
    ∀ k ∈ Z m (e p) (e q), k ≤ max p q := by
  induction m with
  | zero =>
      intro k hk
      exact (mem_e_le hk).trans (Nat.le_max_right p q)
  | succ m ih =>
      intro k hk
      obtain ⟨r, _hr, hpair⟩ := hk
      exact (pair_le_right r k).trans
        ((mem_e_le hpair).trans (Nat.le_max_left p q))

end DomainTheory.DataTypesAsLattices
