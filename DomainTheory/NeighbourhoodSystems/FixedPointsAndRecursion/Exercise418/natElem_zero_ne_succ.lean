/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example43
public import DomainTheory.Neighborhood.Exercise418.Basic
public import DomainTheory.Neighborhood.Exercise418.natElem_injective

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise418

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap Example43


/-- **Exercise 4.18 (Scott 1981, PRG-19).** `0̂` is not a numeral successor. -/
theorem natElem_zero_ne_succ (k : ℕ) : natElem 0 ≠ natElem (k + 1) := fun h =>
  Nat.succ_ne_zero k (natElem_injective h).symm

end DomainTheory.Neighborhood.Exercise418
