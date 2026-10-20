/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise407
public import DomainTheory.Neighborhood.Exercise509.Basic
public import DomainTheory.Neighborhood.Exercise509.iterElem_succ
public import DomainTheory.Neighborhood.Exercise509.iterElem_zerou27

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `(f²)ⁿ(⊥) = f^{2n}(⊥)`. -/
theorem comp_self_iterElem (f : ApproximableMap V V) (n : ℕ) :
    (f.comp f).iterElem n = f.iterElem (2 * n) := by
  induction n with
  | zero => rw [iterElem_zero', Nat.mul_zero, iterElem_zero']
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [iterElem_succ, ih, toElementMap_comp, h2, iterElem_succ, iterElem_succ]

end ApproximableMap
end DomainTheory.Neighborhood
