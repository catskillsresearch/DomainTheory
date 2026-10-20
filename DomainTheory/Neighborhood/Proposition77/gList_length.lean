/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example61
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Proposition77.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77











variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)



































theorem gList_length (step : ℕ → ℕ) (w : ℕ) : (gList step w).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => rw [gList, List.length_cons, ih]

end Proposition77
end DomainTheory.Neighborhood
