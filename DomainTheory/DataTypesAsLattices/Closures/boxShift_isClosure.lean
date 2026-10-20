/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxShift


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_isClosure {a : Pomega} (ha : IsClosure a) :
    IsClosure (boxShift a) :=
  ⟨Icomb_subset_boxShift ha, boxShift_isRetract ha.2⟩

end DomainTheory.DataTypesAsLattices
