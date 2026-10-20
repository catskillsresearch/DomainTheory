/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxShift

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_isClosure {a : Pomega} (ha : IsClosure a) :
    IsClosure (boxShift a) :=
  ⟨Icomb_subset_boxShift ha, boxShift_isRetract ha.2⟩

end DomainTheory.DataTypesAsLattices
