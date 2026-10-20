/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.theorem_4_5_strict


namespace DomainTheory.DataTypesAsLattices

















































/-- **Scott 1976, Theorem 4.5 (The sum theorem), core.** -/
theorem theorem_4_5 :
    dcondSet botElem
        (pairSeq (ofNat 0) (funOf a botElem))
        (pairSeq (ofNat 1) (funOf b botElem)) = botElem ∧
      IsRetract botElem :=
  ⟨theorem_4_5_strict a b, bot_isRetract⟩

end DomainTheory.DataTypesAsLattices
