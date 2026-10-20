/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
import DomainTheory.DataTypesAsLattices.Retracts.intR_idem
import DomainTheory.DataTypesAsLattices.Retracts.intR_isGraph


namespace DomainTheory.DataTypesAsLattices














































theorem intR_isRetract : IsRetract intR := by
  change intR = graph (fun x => funOf intR (funOf intR x))
  refine intR_isGraph.trans ?_
  apply graph_ext
  intro x
  exact (intR_idem x).symm

end DomainTheory.DataTypesAsLattices
