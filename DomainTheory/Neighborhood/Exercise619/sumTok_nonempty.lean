/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example62
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise619.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example62 ExampleB

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}











variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}






/-- The concrete sum is again `∅`-free (an object of Scott's category). -/
theorem sumTok_nonempty : ∀ W, (sumTok D₀ D₁ h₀ h₁).mem W → W.Nonempty :=
  fun _ h => sumTok_mem_nonempty h

end Exercise619
end DomainTheory.Neighborhood
