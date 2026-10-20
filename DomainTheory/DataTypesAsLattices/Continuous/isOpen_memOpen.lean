/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.Bases
import Mathlib.Topology.Order
import DomainTheory.DataTypesAsLattices.Pomega
import DomainTheory.DataTypesAsLattices.Continuous.Basic


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








theorem isOpen_memOpen (k : ℕ) : IsOpen (memOpen k) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨k, rfl⟩

end DomainTheory.DataTypesAsLattices
