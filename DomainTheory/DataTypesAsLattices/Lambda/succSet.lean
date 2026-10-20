/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Table 2.** Successor `x + 1 = {n + 1 | n ∈ x}`. -/
def succSet (x : Pomega) : Pomega :=
  {k | ∃ n ∈ x, k = n + 1}

end DomainTheory.DataTypesAsLattices
