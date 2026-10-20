/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.eq_4_45


namespace DomainTheory.DataTypesAsLattices

















































theorem Hcomb_decode (τ : LambTerm) :
    funOf Hcomb (encodeExp τ) = Htyped τ :=
  (eq_4_45 τ).2.2
end DomainTheory.DataTypesAsLattices
