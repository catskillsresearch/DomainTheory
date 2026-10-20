/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices



theorem pairSeq_app_one (x y : Pomega) : funOf (pairSeq x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
