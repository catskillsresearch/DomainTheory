/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.theorem_5_3
import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_arrowR


namespace DomainTheory.DataTypesAsLattices
































theorem theorem_5_3_closure {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsClosure (arrowR a b) :=
  ⟨Icomb_subset_arrowR ha hb, theorem_5_3 ha hb⟩

end DomainTheory.DataTypesAsLattices
