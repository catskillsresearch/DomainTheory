/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app
import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive


namespace DomainTheory.DataTypesAsLattices































theorem Icomb_subset_boxShift {a : Pomega} (ha : IsClosure a) :
    Icomb ⊆ boxShift a :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxShift_app]
    exact boxShift_expansive ha (e n)

end DomainTheory.DataTypesAsLattices
