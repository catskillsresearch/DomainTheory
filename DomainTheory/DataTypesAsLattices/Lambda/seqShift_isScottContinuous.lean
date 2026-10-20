/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
import DomainTheory.DataTypesAsLattices.Lambda.seqFun_right_isScottContinuous


namespace DomainTheory.DataTypesAsLattices








































theorem seqShift_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun z => seqFun u (succSet z)) :=
  theorem_1_3 (seqFun_right_isScottContinuous u) succSet_isScottContinuous

end DomainTheory.DataTypesAsLattices
