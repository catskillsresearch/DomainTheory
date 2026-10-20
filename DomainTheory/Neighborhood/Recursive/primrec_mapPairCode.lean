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
import DomainTheory.Neighborhood.Recursive.primrec_mapPairStp


namespace Domain.Recursive



























































































































theorem primrec_mapPairCode : Nat.Primrec (fun t => mapPairCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_mapPairStp Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq (fun _ => rfl)

end Domain.Recursive
