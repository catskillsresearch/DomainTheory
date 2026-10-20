/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Icomb_isClosure
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, (5.2).** `I ⊆ I ∘→ I`. -/
theorem eq_5_2 : Icomb ⊆ arrowR Icomb Icomb :=
  Icomb_subset_arrowR Icomb_isClosure Icomb_isClosure

end DomainTheory.DataTypesAsLattices
