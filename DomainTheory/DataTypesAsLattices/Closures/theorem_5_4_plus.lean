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
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_isRetract
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_boxPlus

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 (sum half).** If `a` and `b` are closure
operations then so is `a ⊞ b`. -/
theorem theorem_5_4_plus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (boxPlus a b) :=
  ⟨Icomb_subset_boxPlus ha hb, boxPlus_isRetract ha.2 hb.2⟩

end DomainTheory.DataTypesAsLattices
