/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_10

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem squarePair_inj {x x' y y' : Pomega}
    (h : squarePair x y = squarePair x' y') : x = x' ∧ y = y' :=
  ⟨(eq_5_9 x y).symm.trans ((congrArg squareFst h).trans (eq_5_9 x' y')),
    (eq_5_10 x y).symm.trans ((congrArg squareSnd h).trans (eq_5_10 x' y'))⟩

end DomainTheory.DataTypesAsLattices
