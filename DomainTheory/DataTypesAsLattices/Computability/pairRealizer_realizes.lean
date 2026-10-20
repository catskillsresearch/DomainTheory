/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.pairComb_app


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


































theorem pairRealizer_realizes {u v : Pomega} {p q : ℕ → ℕ}
    (hu : Realizes u p) (hv : Realizes v q) :
    Realizes (pairRealizer u v) (fun n => Nat.pair (p n) (q n)) := fun n => by
  rw [pairRealizer, Scomb_beta3, Scomb_beta3, Kcomb_beta2,
    hu, hv, pairComb_app]

end DomainTheory.DataTypesAsLattices
