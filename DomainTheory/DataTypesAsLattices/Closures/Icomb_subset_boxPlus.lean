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
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_expansive


namespace DomainTheory.DataTypesAsLattices































theorem Icomb_subset_boxPlus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxPlus a b :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxPlus_app]
    exact boxPlus_expansive ha hb (e n)

end DomainTheory.DataTypesAsLattices
