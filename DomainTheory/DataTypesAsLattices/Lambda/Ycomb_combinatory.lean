/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_closed
import DomainTheory.DataTypesAsLattices.Lambda.Yterm_interp


namespace DomainTheory.DataTypesAsLattices


















































theorem Ycomb_combinatory : IsCombinatory Ycomb := by
  simpa [Yterm_interp] using theorem_2_4_closed Yterm

end DomainTheory.DataTypesAsLattices
