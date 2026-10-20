/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Exercise216.Basic
import DomainTheory.Neighborhood.Exercise216.key


namespace DomainTheory.Neighborhood.Exercise216

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB




/-- **Exercise 2.16, second half.** `parityMap` is the *unique* approximable map `B → T`
satisfying `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = parityMap` to matching relations on cones,
which is exactly `key` read through `rel_iff_mem_principal`/`parityMap_rel_cone`. -/
theorem eq_parityMap_of_satisfies {g : ApproximableMap B Example23.T}
    (hg : SatisfiesParityEquations g) : g = Example23.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Example23.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Example23.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Example23.parityMap.rel_dom hr) hX⟩

end DomainTheory.Neighborhood.Exercise216
