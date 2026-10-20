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


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

























































theorem unionBits_eq : ∀ ks : List ℕ, unionBits ks = {n | n ∈ ks}
  | [] => by simp [unionBits, botElem]
  | k :: ks => by
    ext n
    simp [unionBits, unionBits_eq ks, ofNat]

end DomainTheory.DataTypesAsLattices
