/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Definition711
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Proposition710
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Lemma615
import Mathlib.Tactic
import DomainTheory.Neighborhood.Proposition712.Basic
import DomainTheory.Neighborhood.Proposition712.hasTop_of_trianglelefteq_powerDomain
import DomainTheory.Neighborhood.Proposition712.Vshape_not_hasTop


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive



namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}







/-- **Proposition 7.12, Part C is FALSE in general.** The flat two-point domain `Vshape` is *not* a
subdomain of its own Smyth power domain: `Vshape ⋬ ℙ(Vshape)`. (Contrast Parts A, B, D, which hold
for every `𝒟`.) -/
theorem vshape_not_trianglelefteq_powerDomain : ¬ (Vshape ⊴ Vshape.PowerDomain) := fun h =>
  Vshape_not_hasTop (hasTop_of_trianglelefteq_powerDomain h)

end Counterexample712C
end DomainTheory.Neighborhood
