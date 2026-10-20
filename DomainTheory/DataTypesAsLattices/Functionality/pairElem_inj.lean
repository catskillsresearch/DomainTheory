/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj


namespace DomainTheory.DataTypesAsLattices



theorem pairElem_inj {x y x' y' : Pomega} (h : pairElem x y = pairElem x' y') :
    x = x' ∧ y = y' :=
  pairSeq_inj h

end DomainTheory.DataTypesAsLattices
