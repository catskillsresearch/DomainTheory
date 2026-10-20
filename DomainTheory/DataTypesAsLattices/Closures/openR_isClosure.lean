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
public import DomainTheory.DataTypesAsLattices.Closures.openR_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_openR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































/-- **Scott 1976, (4.6) / §5.** `open` is a closure. -/
theorem openR_isClosure : IsClosure openR :=
  ⟨Icomb_subset_openR, openR_isRetract⟩

end DomainTheory.DataTypesAsLattices
