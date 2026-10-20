module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Submonoid.Basic
import all Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.Algebra.Group.Nat.Defs
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.F
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise417.base_subset_F

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise417

open Pointwise

open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

theorem one_mem_F (a b : S) (x : Set S) : (1 : S) ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_left _ rfl)

end DomainTheory.NeighbourhoodSystems.Exercise417
