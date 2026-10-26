module

public import DomainTheory.DataTypesAsLattices.Pomega.pair
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
