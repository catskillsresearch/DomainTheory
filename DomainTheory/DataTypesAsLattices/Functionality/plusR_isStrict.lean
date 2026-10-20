/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_app_bot


namespace DomainTheory.DataTypesAsLattices















theorem plusR_isStrict (a b : Pomega) : IsStrict (plusR a b) :=
  plusR_app_bot a b

end DomainTheory.DataTypesAsLattices
