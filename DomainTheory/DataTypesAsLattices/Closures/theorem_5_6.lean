/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Vcomb_isRetract


namespace DomainTheory.DataTypesAsLattices
































/-- **Scott 1976, Theorem 5.6 (The limit theorem for algebraic lattices).**
`(λf : V∘→V. Y(f)) : (V∘→V) ∘→ V`. -/
theorem theorem_5_6 {f : Pomega} (hf : typed f (arrowR Vcomb Vcomb)) :
    typed (funOf Ycomb f) Vcomb := by
  set y := funOf Ycomb f
  have hy : y = funOf f y := Ycomb_unfold f
  have hf' : ∀ x, funOf f x = funOf Vcomb (funOf f (funOf Vcomb x)) := by
    intro x
    simpa [comp_app] using congrArg (fun w => funOf w x) (typed_of_arrowR hf)
  have hyV : y = funOf Vcomb (funOf f (funOf Vcomb y)) :=
    hy.trans (hf' y)
  have h1 : funOf Vcomb y = funOf Vcomb (funOf f y) :=
    congrArg (funOf Vcomb) hy
  have h2 : funOf Vcomb (funOf f y) =
      funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) :=
    congrArg (funOf Vcomb) (hf' y)
  have h3 : funOf Vcomb (funOf Vcomb (funOf f (funOf Vcomb y))) =
      funOf Vcomb (funOf f (funOf Vcomb y)) :=
    retract_app Vcomb_isRetract _
  exact (h1.trans (h2.trans (h3.trans hyV.symm))).symm

end DomainTheory.DataTypesAsLattices
