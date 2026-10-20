/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices















































theorem hVar_isScottContinuous_t (e : Pomega) :
    IsScottContinuous (fun t => hVar e t) :=
  funOf_isScottContinuous_left (expPayload e)

end DomainTheory.DataTypesAsLattices
