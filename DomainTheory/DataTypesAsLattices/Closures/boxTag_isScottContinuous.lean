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

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxTag_isScottContinuous (i : ℕ) : IsScottContinuous (boxTag i) := by
  have hfun : boxTag i = fun z => condSet z (ofNat i) (ofNat i) := rfl
  rw [hfun]
  exact condSet_isScottContinuous_left (ofNat i) (ofNat i)

end DomainTheory.DataTypesAsLattices
