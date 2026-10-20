/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boool
import DomainTheory.DataTypesAsLattices.Closures.boool_isRetract


namespace DomainTheory.DataTypesAsLattices



































/-- **Scott 1976, (5.3).** `boool` is a closure. -/
theorem boool_isClosure : IsClosure boool :=
  ⟨Icomb_subset_boool, boool_isRetract⟩

end DomainTheory.DataTypesAsLattices
