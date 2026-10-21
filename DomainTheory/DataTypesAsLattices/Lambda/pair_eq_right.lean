/-ai
If the pair of n and m equals m, then both n and m are zero.

The pair equation, rewritten by the triangle formula for pairing, says that the triangle number of n + m, added to m, equals m, so that triangle number is zero. The lemma that a zero triangle number has zero argument gives n + m = 0, and therefore both n and m are zero.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.triangle_eq_zero

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem pair_eq_right {n m : ℕ} (h : pair n m = m) : n = 0 ∧ m = 0 := by
  have : triangle (n + m) = 0 := by
    have h' : triangle (n + m) + m = m := by simpa [pair_eq_triangle] using h
    omega
  have : n + m = 0 := triangle_eq_zero this
  omega

end DomainTheory.DataTypesAsLattices
