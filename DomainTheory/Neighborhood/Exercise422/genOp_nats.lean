/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise414
import DomainTheory.Neighborhood.Theorem46
import DomainTheory.Neighborhood.Exercise422.Basic
import DomainTheory.Neighborhood.Exercise422.genOp_monotone


namespace DomainTheory.Neighborhood.Exercise422

open DomainTheory.Neighborhood DomainTheory.Neighborhood.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)



theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)

end DomainTheory.Neighborhood.Exercise422
