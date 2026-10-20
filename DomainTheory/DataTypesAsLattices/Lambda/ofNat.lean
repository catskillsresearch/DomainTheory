/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
module

public import DomainTheory.DataTypesAsLattices.Embedding

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Scott's integer convention: `n = {n}` as an element of `Pω`. -/
def ofNat (n : ℕ) : Pomega := {n}

end DomainTheory.DataTypesAsLattices
