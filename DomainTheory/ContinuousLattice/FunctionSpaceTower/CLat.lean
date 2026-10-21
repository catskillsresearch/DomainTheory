/-ai
A bundled complete lattice is a type together with a complete-lattice structure. The bundle lets the function-space tower be defined by recursion on the natural numbers, with each successor level depending on the lattice structure of the preceding level.
ai-/
module


public import DomainTheory.ContinuousLattice.InverseLimits
public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Topology.Homeomorph.Defs
import all Mathlib.Topology.Homeomorph.Defs

@[expose] public section

universe u

namespace DomainTheory.ContinuousLattice

/-- A complete lattice bundled with its instance, used to define the function-space tower by
recursion on `ℕ` (the type at level `n+1` depends on the lattice structure at level `n`). -/
structure CLat : Type (u + 1) where
  carrier : Type u
  [str : CompleteLattice carrier]

end DomainTheory.ContinuousLattice
