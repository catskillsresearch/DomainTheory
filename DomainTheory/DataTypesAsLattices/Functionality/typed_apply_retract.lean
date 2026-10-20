/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices

































theorem typed_apply_retract {a x : Pomega} (ha : IsRetract a) :
    typed (funOf a x) a :=
  (retract_app ha x).symm

end DomainTheory.DataTypesAsLattices
