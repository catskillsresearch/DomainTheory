/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Recursive
import DomainTheory.Neighborhood.RationalPrimrec.Basic


namespace DomainTheory.Neighborhood

open Domain.Recursive













theorem qDen_pos (c : ℕ) : 0 < qDen c := Nat.succ_pos _

end DomainTheory.Neighborhood
