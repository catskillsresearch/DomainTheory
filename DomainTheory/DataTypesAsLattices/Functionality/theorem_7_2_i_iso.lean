/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices












/-- The spaces of `E_a` and of `{⟨x, y⟩ | a(x) = a(y)}` are isomorphic:
classes of the kernel are represented uniquely by range elements. -/
theorem theorem_7_2_i_iso {a : Pomega} (ha : IsRetract a) (x y : Pomega) :
    funOf a x = funOf a y ↔ (Ea a).rel (funOf a x) (funOf a y) := by
  constructor
  · intro h
    refine ⟨?_, ?_, h⟩
    · exact (retract_app ha x).symm
    · exact (retract_app ha y).symm
  · intro h
    exact h.2.2

end DomainTheory.DataTypesAsLattices
