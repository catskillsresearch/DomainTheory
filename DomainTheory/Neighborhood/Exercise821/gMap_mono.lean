/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717Part2
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Proposition810
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise821.Basic
import DomainTheory.Neighborhood.Exercise821.GRelu2emono_uv


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **`gMap` is monotone in `u`, `v`.** -/
theorem gMap_mono (hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') : gMap u v hD ≤ gMap u' v' hD := by
  rw [ApproximableMap.le_iff]
  intro W Z h
  exact GRel.mono_uv hD hu hv h

end DomainTheory.Neighborhood
