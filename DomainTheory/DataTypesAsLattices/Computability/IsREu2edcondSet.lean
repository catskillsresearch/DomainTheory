/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.IsREu2etop
import DomainTheory.DataTypesAsLattices.Computability.IsREu2econdSet


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.dcondSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (dcondSet z x y) :=
  IsRE.condSet hz (IsRE.condSet hz hx IsRE.top) (IsRE.condSet hz IsRE.top hy)

end DomainTheory.DataTypesAsLattices
