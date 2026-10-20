/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_botCode
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_myhillCase2Code

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code













theorem valNat_myhillCase2Code_bot (j n : ℕ) :
    valNat (myhillCase2Code j n botCode) = e j := by
  rw [valNat_myhillCase2Code, valNat_botCode, eq_2_7_bot]
  simp [botElem]

end DomainTheory.DataTypesAsLattices
