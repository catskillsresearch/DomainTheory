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
import DomainTheory.Neighborhood.Exercise821.iSharp_comp_jSharp_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}



variable {hD : ∀ X, D.mem X → X.Nonempty}








variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}







/-- **`U§ ⊴ U`.** -/
theorem dsharpU_trianglelefteq_U : Dsharp U U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iSharp jSharp jSharp_comp_iSharp iSharp_comp_jSharp_le

end DomainTheory.Neighborhood
