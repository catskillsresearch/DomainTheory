/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RationalPrimrec.Basic
import DomainTheory.Neighborhood.RationalPrimrec.primrec_ratLeCode


namespace DomainTheory.Neighborhood

open Domain.Recursive



















theorem primrec_ratMinCode : Nat.Primrec ratMinCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.left Nat.Primrec.right

end DomainTheory.Neighborhood
