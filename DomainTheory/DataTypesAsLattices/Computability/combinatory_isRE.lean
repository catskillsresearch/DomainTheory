/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.IsREu2ezeroC
import DomainTheory.DataTypesAsLattices.Computability.IsREu2efunOf
import DomainTheory.DataTypesAsLattices.Computability.IsREu2esucC
import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredC
import DomainTheory.DataTypesAsLattices.Computability.IsREu2eKcomb
import DomainTheory.DataTypesAsLattices.Computability.IsREu2econdC
import DomainTheory.DataTypesAsLattices.Computability.IsREu2eScomb


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

/-- Combinatory elements are r.e. (one direction of the appendix equivalence). -/
theorem combinatory_isRE {u : Pomega} (hu : IsCombinatory u) : IsRE u := by
  induction hu with
  | zero => exact IsRE.zeroC
  | suc => exact IsRE.sucC
  | pred => exact IsRE.predC
  | cond => exact IsRE.condC
  | K => exact IsRE.Kcomb
  | S => exact IsRE.Scomb
  | app _ _ iu iv => exact IsRE.funOf iu iv

end DomainTheory.DataTypesAsLattices
