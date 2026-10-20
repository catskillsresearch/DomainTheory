/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RecursiveCross.Basic
import DomainTheory.Neighborhood.RecursiveCross.primrec_consStep2


namespace Domain.Recursive




theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_consStep2 (Nat.Primrec.const 0) Nat.Primrec.right
    Nat.Primrec.left).of_eq fun _ => rfl

end Domain.Recursive
