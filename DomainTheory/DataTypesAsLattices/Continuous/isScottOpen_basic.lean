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






theorem isScottOpen_basic (n : ℕ) : IsScottOpen (basicNhhd n) :=
  ⟨{n}, by ext x; simp [basicNhhd]⟩

end DomainTheory.DataTypesAsLattices
