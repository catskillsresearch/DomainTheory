/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous


namespace DomainTheory.DataTypesAsLattices



















































theorem termShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun t => funOf u (succSet t)) :=
  theorem_1_3 (funOf_isScottContinuous u) succSet_isScottContinuous

end DomainTheory.DataTypesAsLattices
