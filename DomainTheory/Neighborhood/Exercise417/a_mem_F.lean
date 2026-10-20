/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Nat.Defs
import DomainTheory.Neighborhood.Exercise417.Basic


namespace DomainTheory.Neighborhood.Exercise417

open Pointwise
open DomainTheory.Neighborhood.Exercise414

variable {S : Type*} [Monoid S]





theorem a_mem_F (a b : S) (x : Set S) : a ∈ F a b x :=
  base_subset_F a b x (Set.mem_union_right _ (Set.mem_insert _ _))

end DomainTheory.Neighborhood.Exercise417
