/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3_closure


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.24).** Function space of closures is a closure. -/
theorem eq_5_24 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (arrowR a b) Vcomb :=
  (theorem_5_5_universe.2 (arrowR a b)).mp
    (theorem_5_3_closure ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
