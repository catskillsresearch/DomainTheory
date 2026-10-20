/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Hfun

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.45).** `ℋ : exp → (env → lamb)`, the retract of the
least fixed point of the syntax-directed continuous operator. -/
def Hcomb : Pomega :=
  funOf (arrowR expR (arrowR envR lambR)) Hfun

end DomainTheory.DataTypesAsLattices
