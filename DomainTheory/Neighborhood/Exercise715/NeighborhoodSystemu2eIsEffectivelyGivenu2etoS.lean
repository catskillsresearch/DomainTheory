/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Exercise316
import DomainTheory.Neighborhood.Exercise715.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}






theorem NeighborhoodSystem.IsEffectivelyGiven.toS {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.IsEffectivelyGivenS :=
  h.elim fun P => ⟨P.toScott⟩

end DomainTheory.Neighborhood
