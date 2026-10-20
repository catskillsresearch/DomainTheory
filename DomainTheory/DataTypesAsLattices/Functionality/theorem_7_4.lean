/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_i
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_4_unique


namespace DomainTheory.DataTypesAsLattices






























/-- **Scott 1976, Theorem 7.4 (The iterator theorem).**
The functionality is both satisfied by and globally characterizes the
iterators. -/
theorem theorem_7_4 :
    (∀ A n, (arrowE (arrowE A A) (arrowE A A)).mem (Zcomb n)) ∧
      ∀ z,
        (∀ f, funOf z f = funOf z (graph (fun y => funOf f y))) →
        (∀ A, (arrowE (arrowE A A) (arrowE A A)).mem z) →
        ∃ n, z = Zcomb n :=
  ⟨theorem_7_4_i, theorem_7_4_unique⟩

end DomainTheory.DataTypesAsLattices
