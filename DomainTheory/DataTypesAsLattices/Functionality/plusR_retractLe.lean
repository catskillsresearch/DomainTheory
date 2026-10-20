/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_13


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, Theorem 4.5 (iii).** `⊕` preserves `⊑`. -/
theorem plusR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (plusR a b) (plusR a' b') := by
  constructor
  · have h : plusR (comp a a') (comp b b') = plusR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_13 a b a' b').trans h).symm
  · have h : plusR (comp a' a) (comp b' b) = plusR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_13 a' b' a b).trans h).symm

end DomainTheory.DataTypesAsLattices
