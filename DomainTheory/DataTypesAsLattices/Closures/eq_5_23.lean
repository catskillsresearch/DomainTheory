/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_4_plus
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.23).** Boxed sum of closures is a closure, so the map
is typed on `V`. -/
theorem eq_5_23 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxPlus a b) Vcomb :=
  (theorem_5_5_universe.2 (boxPlus a b)).mp
    (theorem_5_4_plus ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
