/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_zero
import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
import DomainTheory.DataTypesAsLattices.Functionality.seq4_app


namespace DomainTheory.DataTypesAsLattices
































theorem seq4_app_one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [seq4_app, condSet_ofNat_one, predSet_ofNat_succ, condSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
