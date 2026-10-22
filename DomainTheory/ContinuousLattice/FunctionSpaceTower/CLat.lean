module
public import Mathlib.Order.CompleteLattice.Defs



@[expose] public section

universe u

namespace DomainTheory.ContinuousLattice

/-- A complete lattice bundled with its instance, used to define the function-space tower by
recursion on `ℕ` (the type at level `n+1` depends on the lattice structure at level `n`). -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

end DomainTheory.ContinuousLattice
