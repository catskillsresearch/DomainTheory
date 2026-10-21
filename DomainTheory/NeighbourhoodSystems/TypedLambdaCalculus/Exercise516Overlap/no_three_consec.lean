/-ai
There are no three consecutive equal Thue–Morse bits: the bits at j, j + 1, and j + 2 are not all equal.

Equality of consecutive bits forces both j and j + 1 to be odd. The two odd representations are arithmetically incompatible.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.odd_of_consec_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems


/-- **No three consecutive equal symbols** (the period-`1` case): `¬ (tm j = tm (j+1) ∧
tm (j+1) = tm (j+2))`. If both held, `j` and `j+1` would both be odd. -/
theorem no_three_consec (j : ℕ) : ¬ (tm j = tm (j + 1) ∧ tm (j + 1) = tm (j + 2)) := by
  rintro ⟨h1, h2⟩
  have hj : Odd j := odd_of_consec_eq h1
  have hj1 : Odd (j + 1) := odd_of_consec_eq h2
  rcases hj with ⟨a, rfl⟩
  rcases hj1 with ⟨b, hb⟩
  omega

end DomainTheory.NeighbourhoodSystems.Exercise516
