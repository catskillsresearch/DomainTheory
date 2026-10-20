/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices


















theorem compactFixedBelow_sUnion {a : Pomega} (ha : IsClosure a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' compactFixedBelow a x) := by
  rw [← retractBasis_eq_compactFixedBelow ha x]
  exact retractBasis_sUnion ha.2 x

end DomainTheory.DataTypesAsLattices
