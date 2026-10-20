/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairElem_fst
import DomainTheory.DataTypesAsLattices.Functionality.pairElem_snd
import DomainTheory.DataTypesAsLattices.Functionality.condSet_ofNat_one
import DomainTheory.DataTypesAsLattices.Functionality.sumMed_app


namespace DomainTheory.DataTypesAsLattices















theorem sumMed_app_inr (f g x : Pomega) :
    funOf (sumMed f g) (pairElem (ofNat 1) x) = funOf g x := by
  rw [sumMed_app, pairElem_fst, pairElem_snd, condSet_ofNat_one]

end DomainTheory.DataTypesAsLattices
