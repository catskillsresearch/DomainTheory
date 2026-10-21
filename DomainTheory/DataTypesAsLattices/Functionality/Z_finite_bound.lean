/-ai
Every natural number belonging to the m-fold iterator of the finite set coded by p, started at the finite set coded by q, is at most the maximum of p and q.

Induct on the stage. At stage zero, membership in the finite set coded by q bounds the number by q and hence by the maximum. At a successor stage the membership unpacks a witness and a pair code in the finite set coded by p. The right-component bound, membership in a finite set, and comparison with the left-hand maximum bound the number by the maximum of p and q.
ai-/
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
