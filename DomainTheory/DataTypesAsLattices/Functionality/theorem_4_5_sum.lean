/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_isStrict
import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.plusR_typed_iff


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 4.5 (The sum theorem).** -/
theorem theorem_4_5_sum {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (plusR a b) ∧ IsStrict (plusR a b) ∧
      (∀ u, typed u (plusR a b) ↔
        u = botElem ∨ u = topElem ∨
          (∃ x, u = pairSeq (ofNat 0) x ∧ typed x a) ∨
            (∃ y, u = pairSeq (ofNat 1) y ∧ typed y b)) :=
  ⟨plusR_isRetract ha hb, plusR_isStrict a b, fun _u => plusR_typed_iff ha hb⟩

end DomainTheory.DataTypesAsLattices
