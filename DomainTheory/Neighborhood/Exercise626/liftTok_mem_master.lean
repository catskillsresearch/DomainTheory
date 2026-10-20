/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise621
import DomainTheory.Neighborhood.Exercise626.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise619
open DomainTheory.Neighborhood.Example62 DomainTheory.Neighborhood.ExampleB
open DomainTheory.Neighborhood.Exercise510

namespace Exercise619

variable {D : NeighborhoodSystem Str}










variable {hD : ∀ X, D.mem X → X.Nonempty}

theorem liftTok_mem_master : (liftTok D hD).mem (liftTokMaster D) := Or.inl rfl

end Exercise619
end DomainTheory.Neighborhood
