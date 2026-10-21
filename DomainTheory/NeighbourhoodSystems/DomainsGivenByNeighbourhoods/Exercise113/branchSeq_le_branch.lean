/-ai
Each finite approximation along an infinite binary path approximates the branch of that path.

This is the general fact that each term of a monotone sequence lies below its ascending union, applied to the finite approximations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB








/-- Every finite approximation `(p ↾ n)⊥` approximates the limit element `branch p`. -/
theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n

end DomainTheory.NeighbourhoodSystems.Exercise113
