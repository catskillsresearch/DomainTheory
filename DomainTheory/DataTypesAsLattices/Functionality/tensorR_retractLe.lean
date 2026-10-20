/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_12


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4 (iii).** `⊗` preserves `⊑`. -/
theorem tensorR_retractLe {a b a' b' : Pomega}
    (hab : retractLe a a') (hbb : retractLe b b') :
    retractLe (tensorR a b) (tensorR a' b') := by
  constructor
  · have h : tensorR (comp a a') (comp b b') = tensorR a b := by
      rw [← hab.1, ← hbb.1]
    exact ((eq_4_12 a b a' b').trans h).symm
  · have h : tensorR (comp a' a) (comp b' b) = tensorR a b := by
      rw [← hab.2, ← hbb.2]
    exact ((eq_4_12 a' b' a b).trans h).symm

end DomainTheory.DataTypesAsLattices
