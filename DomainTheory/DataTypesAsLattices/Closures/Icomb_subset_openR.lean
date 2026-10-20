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
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
public import DomainTheory.DataTypesAsLattices.Closures.openR_app
public import DomainTheory.DataTypesAsLattices.Closures.openR_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem Icomb_subset_openR : Icomb ⊆ openR :=
  Icomb_subset_graph.mpr fun n => by
    rw [← openR_app]
    exact openR_expansive (e n)

end DomainTheory.DataTypesAsLattices
