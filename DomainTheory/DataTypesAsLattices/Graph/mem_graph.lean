/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Continuous
import DomainTheory.DataTypesAsLattices.Graph.Basic


namespace DomainTheory.DataTypesAsLattices




theorem mem_graph {f : Pomega → Pomega} {p : ℕ} :
    p ∈ graph f ↔ ∃ n m, p = pair n m ∧ m ∈ f (e n) := Iff.rfl

end DomainTheory.DataTypesAsLattices
