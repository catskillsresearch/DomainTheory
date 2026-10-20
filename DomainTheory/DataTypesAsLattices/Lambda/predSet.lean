/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Predecessor `x − 1 = {n | n + 1 ∈ x}`. -/
def predSet (x : Pomega) : Pomega :=
  {k | k + 1 ∈ x}

end DomainTheory.DataTypesAsLattices
