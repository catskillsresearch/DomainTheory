/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.primRecZeroC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.sqrtStepC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

























theorem sqrtC_combinatory : IsCombinatory sqrtC :=
  .app
    (.app .S
      (.app (.app .S (.app .K primRecZeroC_combinatory))
        sqrtStepC_combinatory))
    (.app (.app .S .K) .K)

end DomainTheory.DataTypesAsLattices
