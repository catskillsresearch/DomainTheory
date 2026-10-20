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
import DomainTheory.DataTypesAsLattices.Enumeration.primrec_myhillFilterCode


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code






























theorem primrec_myhillCase1Code (n : ℕ) : Primrec (myhillCase1Code n) :=
  primrec_applyNat.comp
    (primrec_applyNat.comp (Primrec.const interCode) (Primrec.const n))
    primrec_myhillFilterCode

end DomainTheory.DataTypesAsLattices
