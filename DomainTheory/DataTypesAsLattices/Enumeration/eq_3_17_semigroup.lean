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
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_16
import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_17_projections


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






















































/-- Nested positive-branch packaging of (3.17): `ū⁺(v̄⁺(R(x)))`
has first projection `u` and recovers `u(v)(x)` via `L` after
replacing the head by `u(v)`. -/
theorem eq_3_17_semigroup (u v x : Pomega) :
    funOf (barPos u (barPos v (funOf Rcomb x))) (ofNat 1) = u ∧
      funOf Lcomb (barPos (funOf u v) (funOf Rcomb x)) =
        funOf (funOf u v) x :=
  ⟨(eq_3_17_projections u v x).1, eq_3_16 (funOf u v) x⟩

end DomainTheory.DataTypesAsLattices
