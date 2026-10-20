/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_diag_isScottContinuous
import DomainTheory.DataTypesAsLattices.Functionality.plusR_right_isScottContinuous


namespace DomainTheory.DataTypesAsLattices






























theorem treeF_isScottContinuous : IsScottContinuous treeF :=
  theorem_1_3 (f := fun b => plusR botElem b) (g := fun z => tensorR z z)
    (plusR_right_isScottContinuous botElem)
    tensorR_diag_isScottContinuous

end DomainTheory.DataTypesAsLattices
