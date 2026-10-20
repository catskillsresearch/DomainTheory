/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Lemma615
import DomainTheory.Neighborhood.Proposition612
import DomainTheory.Neighborhood.Theorem69
import DomainTheory.Neighborhood.Definition89
import DomainTheory.Neighborhood.Exercise812g4
import DomainTheory.Neighborhood.Exercise817.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}









/-- **Exercise 8.17, Part 1 (`×`).** `iTimes/jTimes` already are the pair `𝒰×𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem prodUU_trianglelefteq_U : prod U U ⊴ U :=
  trianglelefteq_of_projectionPair iTimes jTimes jTimes_comp_iTimes iTimes_comp_jTimes_le

end DomainTheory.Neighborhood
