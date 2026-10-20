/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Exercise626.Basic
import DomainTheory.Neighborhood.Exercise626.liftBot_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}










variable {hD : ∀ X, D.mem X → X.Nonempty}








/-- The fresh bottom is *strictly* below every lifted element. -/
theorem liftBot_lt_liftUp (x : D.Element) : liftBot D hD < liftUp (hD := hD) x := by
  refine lt_of_le_of_ne (liftBot_le _) (fun heq => ?_)
  have hmem : (liftBot D hD).mem (embBit false D.master) := by
    rw [heq]; exact Or.inr ⟨D.master, x.master_mem, rfl⟩
  exact embF_ne_liftTokMaster hmem

end Exercise619
end DomainTheory.Neighborhood
