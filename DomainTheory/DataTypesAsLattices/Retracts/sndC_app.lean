/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices











theorem sndC_app (u : Pomega) : funOf sndC u = funOf u (ofNat 1) :=
  beta (funOf_isScottContinuous_left (ofNat 1)) u

end DomainTheory.DataTypesAsLattices
