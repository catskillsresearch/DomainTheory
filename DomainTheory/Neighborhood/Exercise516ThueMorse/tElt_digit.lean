/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.Neighborhood.Exercise516ThueMorse.Basic
public import DomainTheory.Neighborhood.Exercise516ThueMorse.tmList_succ
public import DomainTheory.Neighborhood.Exercise516ThueMorse.tmList_le_tElt

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise516

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`. -/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h

end DomainTheory.Neighborhood.Exercise516
