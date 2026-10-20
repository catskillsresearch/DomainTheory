/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise617
import DomainTheory.Neighborhood.Exercise617Gen.Basic
import DomainTheory.Neighborhood.Exercise617Gen.Cn_domain_equation


namespace DomainTheory.Neighborhood.Exercise617Gen

set_option linter.unusedSectionVars false

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise510

variable {A : Type} [DecidableEq A]





















































/-- **`Cₙ ≅ 𝟙 + (n+1)·Cₙ`** over the alphabet `Fin (n+1)`. -/
theorem Cfin_domain_equation (n : ℕ) : Cn (Fin (n + 1)) ≅ᴰ CCn (Fin (n + 1)) :=
  Cn_domain_equation (Fin (n + 1))

end DomainTheory.Neighborhood.Exercise617Gen
