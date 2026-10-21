/-ai
If a sequence of subsets of Pω has each stage contained in the next, then an index a less than or equal to b has its stage contained in the stage at b.

Write the difference of b and a as a natural number and induct on it. The zero step is reflexivity of inclusion. The successor step composes the inductive inclusion with the given one-step inclusion.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Graph
public import DomainTheory.DataTypesAsLattices.FixedPoint.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

theorem chain_mono (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    ∀ a b, a ≤ b → xs a ⊆ xs b := by
  intro a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  subst hd
  clear hab
  induction d with
  | zero => simp
  | succ d ih => exact subset_trans ih (hmono _)

end DomainTheory.DataTypesAsLattices
