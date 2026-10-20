/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Recursive
public import DomainTheory.Neighborhood.RationalPrimrec.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive















theorem ratLeCode_le_one (t : ℕ) : ratLeCode t ≤ 1 := isZero_le_one _

end DomainTheory.Neighborhood
