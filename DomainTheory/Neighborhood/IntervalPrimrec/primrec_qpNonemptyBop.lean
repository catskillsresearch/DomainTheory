/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition87
import DomainTheory.Neighborhood.RationalPrimrec
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.IntervalPrimrec.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive







































theorem primrec_qpNonemptyBop : Nat.Primrec qpNonemptyBop :=
  primrec_ratLtCode.comp (Nat.Primrec.left.pair Nat.Primrec.right)

end DomainTheory.Neighborhood
