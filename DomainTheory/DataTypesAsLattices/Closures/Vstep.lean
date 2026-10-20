/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.14).** `V(a)(x) = Y(λy. x ∪ a(y))`. -/
def Vstep (a x : Pomega) (y : Pomega) : Pomega := x ∪ funOf a y

end DomainTheory.DataTypesAsLattices
