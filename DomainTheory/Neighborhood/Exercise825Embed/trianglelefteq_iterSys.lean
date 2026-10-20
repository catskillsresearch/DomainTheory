/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise511
import DomainTheory.Neighborhood.Exercise618
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Exercise825Embed.Basic
import DomainTheory.Neighborhood.Exercise825Embed.head_comp_embedIntoPow
import DomainTheory.Neighborhood.Exercise825Embed.embedIntoPow_comp_head_le


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap DomainTheory.Neighborhood.Exercise511

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 8.25 (Scott 1981, PRG-19): `𝒟 ⊴ 𝒟^∞`**, for every `𝒟`. Specialized to `𝒟 = 𝒰` this is
Scott's remark `𝒰 ⊴ 𝒰^∞`. -/
theorem trianglelefteq_iterSys : V ⊴ iterSys V :=
  trianglelefteq_of_projectionPair (embedIntoPow V) (head V)
    (head_comp_embedIntoPow V) (embedIntoPow_comp_head_le V)

end DomainTheory.Neighborhood
