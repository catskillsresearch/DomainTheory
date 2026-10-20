/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE
import DomainTheory.DataTypesAsLattices.Computability.IsREu2ecombinatory


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4







































theorem IsRE.iff_combinatory {u : Pomega} : IsRE u ↔ IsCombinatory u :=
  ⟨IsRE.combinatory, combinatory_isRE⟩

end DomainTheory.DataTypesAsLattices
