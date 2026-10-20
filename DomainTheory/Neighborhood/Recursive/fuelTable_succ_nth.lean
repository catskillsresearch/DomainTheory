/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic
import DomainTheory.Neighborhood.Recursive.fuelTableStep_nth


namespace Domain.Recursive













































































































































































theorem fuelTable_succ_nth {bodyLookup : ℕ → ℕ} {bound fuel i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTable bodyLookup bound (fuel + 1)) i d =
      bodyLookup (Nat.pair (fuelTable bodyLookup bound fuel) i) :=
  fuelTableStep_nth hi d

end Domain.Recursive
