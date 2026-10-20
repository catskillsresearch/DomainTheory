/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.addC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.subC_combinatory
import DomainTheory.DataTypesAsLattices.Computability.mulC_combinatory


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

















theorem arithEnv_combinatory : ∀ i, IsCombinatory (arithEnv i)
  | 0 => addC_combinatory
  | 1 => mulC_combinatory
  | 2 => subC_combinatory
  | n + 3 => by
    have hbot : funOf predC zeroC = botElem := by
      rw [predC_app]; exact eq_2_6
    simpa [arithEnv, hbot] using
      IsCombinatory.app IsCombinatory.pred IsCombinatory.zero

end DomainTheory.DataTypesAsLattices
