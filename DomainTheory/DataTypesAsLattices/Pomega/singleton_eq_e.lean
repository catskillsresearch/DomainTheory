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
import DomainTheory.DataTypesAsLattices.Pomega.e_pow2


namespace DomainTheory.DataTypesAsLattices












theorem singleton_eq_e (k : ℕ) : ({k} : Pomega) = e (2 ^ k) := (e_pow2 k).symm

end DomainTheory.DataTypesAsLattices
