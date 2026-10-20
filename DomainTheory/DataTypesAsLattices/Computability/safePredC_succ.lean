/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4










theorem safePredC_succ (n : ℕ) : funOf safePredC (ofNat (n + 1)) = ofNat n := by
  simp only [safePredC]
  rw [theorem_2_2_beta]
  simp [interp, envSet, Function.update, eq_2_7_succ, predSet_ofNat_succ]

end DomainTheory.DataTypesAsLattices
