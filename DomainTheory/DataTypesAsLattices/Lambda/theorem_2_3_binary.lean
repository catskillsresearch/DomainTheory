/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.curry2_app


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 2.3 (The reduction theorem), binary case.** -/
theorem theorem_2_3_binary {f : Pomega → Pomega → Pomega}
    (hfx : ∀ y, IsScottContinuous (fun x => f x y))
    (hfy : ∀ x, IsScottContinuous (fun y => f x y)) :
    ∃ u, ∀ x y, funOf (funOf u x) y = f x y :=
  ⟨curry2 f hfx hfy, curry2_app f hfx hfy⟩

end DomainTheory.DataTypesAsLattices
