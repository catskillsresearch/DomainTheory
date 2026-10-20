/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices














































theorem dcondSet_same_ofNat (n : ℕ) (x : Pomega) :
    dcondSet (ofNat n) x x = x :=
  match n with
  | 0 => dcondSet_ofNat_zero x x
  | n + 1 => dcondSet_ofNat_succ n x x

end DomainTheory.DataTypesAsLattices
