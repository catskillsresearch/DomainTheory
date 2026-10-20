/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices


theorem pairElem_fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2_app_zero x y

end DomainTheory.DataTypesAsLattices
