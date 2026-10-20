/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices














































/-- **Scott 1976, Theorem 4.5 (i), strictness of sums.** The zero summand
is always selected on `⊥`. -/
theorem theorem_4_5_strict (a b : Pomega) :
    dcondSet botElem
      (pairSeq (ofNat 0) (funOf a botElem))
      (pairSeq (ofNat 1) (funOf b botElem)) = botElem :=
  dcondSet_bot _ _

end DomainTheory.DataTypesAsLattices
