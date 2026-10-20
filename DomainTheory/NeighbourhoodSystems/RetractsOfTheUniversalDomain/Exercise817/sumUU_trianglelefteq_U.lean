/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem88
public import DomainTheory.Neighborhood.Lemma615
public import DomainTheory.Neighborhood.Proposition612
public import DomainTheory.Neighborhood.Theorem69
public import DomainTheory.Neighborhood.Definition89
public import DomainTheory.Neighborhood.Exercise812g4
public import DomainTheory.Neighborhood.Exercise817.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}









/-- **Exercise 8.17, Part 1 (`+`).** `iPlus/jPlus` (`Definition89.lean`) already *are* the computable
projection pair `𝒰+𝒰 ⇄ 𝒰` needed for 8.9. Bonus: Lemma 6.15 upgrades it to `𝒰+𝒰 ⊴ 𝒰`. -/
theorem sumUU_trianglelefteq_U : sum U U U_mem_nonempty U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iPlus jPlus jPlus_comp_iPlus iPlus_comp_jPlus_le

end DomainTheory.Neighborhood
