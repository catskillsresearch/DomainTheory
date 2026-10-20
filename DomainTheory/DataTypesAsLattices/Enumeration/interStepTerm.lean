/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

/-- A closed LAMBDA term for the body defining binary intersection. -/
def interStepTerm : Term :=
  let omega : Term := .lam 4 (.app (.var 4) (.var 4))
  .lam 0 (.lam 1 (.lam 2
    (.cond (.var 1)
      (.cond (.var 2) .zero (.app omega omega))
      (.succ (.app (.app (.var 0) (.pred (.var 1))) (.pred (.var 2)))))))

end DomainTheory.DataTypesAsLattices
