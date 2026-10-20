/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import DomainTheory.DataTypesAsLattices.Pomega.Basic
import DomainTheory.DataTypesAsLattices.Pomega.e_codeFinset


namespace DomainTheory.DataTypesAsLattices















theorem exists_code (s : Finset ℕ) : ∃ n, e n = (s : Set ℕ) :=
  ⟨codeFinset s, e_codeFinset s⟩

end DomainTheory.DataTypesAsLattices
