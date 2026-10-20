/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.interStep_isScottContinuous


namespace DomainTheory.DataTypesAsLattices





































theorem interC_unfold : interC = interStep interC :=
  (theorem_1_4 interStep_isScottContinuous).1.symm

end DomainTheory.DataTypesAsLattices
