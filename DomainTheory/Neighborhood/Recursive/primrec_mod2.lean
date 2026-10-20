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
import DomainTheory.Neighborhood.Recursive.halfParity_spec
import DomainTheory.Neighborhood.Recursive.primrec_halfParity


namespace Domain.Recursive





















































































theorem primrec_mod2 : Nat.Primrec (fun n => n % 2) :=
  (Nat.Primrec.right.comp primrec_halfParity).of_eq fun n => by
    rw [halfParity_spec, unpair_pair_snd]

end Domain.Recursive
