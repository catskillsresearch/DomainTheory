/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_4
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.22).** Boxed product of closures is a closure, so
the map is typed on `V`. -/
theorem eq_5_22 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxTensor a b) Vcomb :=
  (theorem_5_5_universe.2 (boxTensor a b)).mp
    (theorem_5_4 ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
