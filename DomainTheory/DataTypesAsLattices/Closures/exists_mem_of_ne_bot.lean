/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices































theorem exists_mem_of_ne_bot {x : Pomega} (h : x ≠ botElem) : ∃ m, m ∈ x := by
  by_contra hc
  refine h ?_
  ext n
  simp only [mem_botElem, iff_false]
  exact fun hn => hc ⟨n, hn⟩

end DomainTheory.DataTypesAsLattices
