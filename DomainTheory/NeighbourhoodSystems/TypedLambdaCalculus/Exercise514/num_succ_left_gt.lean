/-ai
The pairing of n + 1 with b is strictly greater than b.

Unfold the pairing. Arithmetic rewrites n + 1 + b as the successor of n + b. Rewriting by that equality and the successor law for triangular numbers, arithmetic gives the strict inequality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513


/-- `num (n+1) b` strictly exceeds its second argument: this is what makes the decode recursion
terminate. `num (n+1) b = T(n+1+b) + b ≥ (n+b+1) + b > b`. -/
theorem num_succ_left_gt (n b : ℕ) : b < num (n + 1) b := by
  unfold num
  have e : n + 1 + b = (n + b) + 1 := by omega
  rw [e, tri_succ]
  omega

end DomainTheory.NeighbourhoodSystems.Exercise514
