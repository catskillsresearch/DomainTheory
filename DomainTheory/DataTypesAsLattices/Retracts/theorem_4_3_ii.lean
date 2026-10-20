/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app


namespace DomainTheory.DataTypesAsLattices






































/-- **Scott 1976, Theorem 4.3 (ii).** `u : a ∘→ b` means `u` is restricted
to `a` and takes values in `b`. -/
theorem theorem_4_3_ii {a b u x : Pomega}
    (hu : typed u (arrowR a b)) (hx : typed x a) :
    typed (funOf u x) b := by
  have hu' : u = comp b (comp u a) := by
    simpa [typed, arrowR_app] using hu
  have : funOf u x = funOf b (funOf u (funOf a x)) := by
    have h1 : funOf u x = funOf (comp b (comp u a)) x :=
      congrArg (fun w => funOf w x) hu'
    rw [h1, comp_app, comp_app]
  rwa [show funOf a x = x from hx.symm] at this

end DomainTheory.DataTypesAsLattices
