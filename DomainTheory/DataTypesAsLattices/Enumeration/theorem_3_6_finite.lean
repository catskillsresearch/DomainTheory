/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.Icomb_SK_app
import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
import DomainTheory.DataTypesAsLattices.Enumeration.singleGenerator_app_zero


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



































/-- **Scott 1976, Theorem 3.6.** `cond(⟨xs⟩)(G)` applied to `0` is the
packed tuple, and `G` is in its degree. -/
theorem theorem_3_6_finite (xs : List Pomega) :
    packList xs ∈ Deg (singleGenerator xs) ∧
      Gcomb ∈ Deg (singleGenerator xs) := by
  constructor
  · refine ⟨funOf (funOf Scomb Icomb_SK) (funOf Kcomb zeroC),
      .app (.app .S (.app (.app .S .K) .K)) (.app .K .zero), ?_⟩
    rw [Scomb_beta3, Icomb_SK_app, Kcomb_beta2, singleGenerator_app_zero]
  · exact (Deg_isSubalgebra (singleGenerator xs)).1

end DomainTheory.DataTypesAsLattices
