/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import DomainTheory.DataTypesAsLattices.Graph

/-!
# Scott 1976, §1 — substitution, fixed points, and the chain lemma
-/

namespace DomainTheory.DataTypesAsLattices

/-- Iterate `f` starting from `⊥`. -/
def iterateBot (f : Pomega → Pomega) : ℕ → Pomega
  | 0 => botElem
  | n + 1 => f (iterateBot f n)

/-- **Scott 1976, Theorem 1.4.** Least fixed point `fix(f) = ⋃_n fⁿ(∅)`. -/
def fix (f : Pomega → Pomega) : Pomega :=
  ⋃ n, iterateBot f n
end DomainTheory.DataTypesAsLattices
