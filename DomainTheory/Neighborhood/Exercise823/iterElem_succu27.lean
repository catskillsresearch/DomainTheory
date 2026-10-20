/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem86
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise816
import DomainTheory.Neighborhood.Exercise823.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}








theorem iterElem_succ' (t : ApproximableMap (funSpace E E) (funSpace E E)) (n : ℕ) :
    t.iterElem (n + 1) = t.toElementMap (t.iterElem n) := by
  show (t.comp (t.iterMap n)).toElementMap (funSpace E E).bot = t.toElementMap (t.iterElem n)
  rw [toElementMap_comp]
  rfl

end Exercise823
end DomainTheory.Neighborhood
