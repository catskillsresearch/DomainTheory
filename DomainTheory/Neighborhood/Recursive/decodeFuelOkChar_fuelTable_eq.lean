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
import DomainTheory.Neighborhood.Recursive.fuelTable_eq_of_recursion


namespace Domain.Recursive


























































































































































































theorem decodeFuelOkChar_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable decodeFuelOkCharLookup bound fuel) c 0 = decodeFuelOkChar fuel c :=
  fuelTable_eq_of_recursion (F := decodeFuelOkChar) (Body := decodeFuelOkCharBody)
    (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold decodeFuelOkCharLookup; simp)
    decodeFuelOkCharBody_local

end Domain.Recursive
