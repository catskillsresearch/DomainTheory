/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.4.** Projections of a
`⊠`-typed point remain typed. -/
theorem typed_of_boxTensor {a b u : Pomega} (hu : typed u (boxTensor a b)) :
    typed (squareFst u) a ∧ typed (squareSnd u) b := by
  have : u = squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) := by
    simpa [typed, boxTensor_app] using hu
  exact ⟨congrArg squareFst this |>.trans (eq_5_9 _ _),
    congrArg squareSnd this |>.trans (eq_5_10 _ _)⟩

end DomainTheory.DataTypesAsLattices
