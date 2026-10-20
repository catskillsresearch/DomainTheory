/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
import DomainTheory.DataTypesAsLattices.Closures.eq_5_10


namespace DomainTheory.DataTypesAsLattices































theorem squarePair_inj {x x' y y' : Pomega}
    (h : squarePair x y = squarePair x' y') : x = x' ∧ y = y' :=
  ⟨(eq_5_9 x y).symm.trans ((congrArg squareFst h).trans (eq_5_9 x' y')),
    (eq_5_10 x y).symm.trans ((congrArg squareSnd h).trans (eq_5_10 x' y'))⟩

end DomainTheory.DataTypesAsLattices
