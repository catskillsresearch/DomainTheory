/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RecursiveCross.Basic
import DomainTheory.Neighborhood.RecursiveCross.primrec_crossOuterStep


namespace Domain.Recursive
















theorem primrec_crossCombine {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossCombine bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossOuterStep hbop) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

end Domain.Recursive
