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









/-- **Exercise 8.17, Part 1 (`→`).** `iArrow/jArrow` already are the pair `𝒰→𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem funSpaceUU_trianglelefteq_U : funSpace U U ⊴ U :=
  trianglelefteq_of_projectionPair iArrow jArrow jArrow_comp_iArrow iArrow_comp_jArrow_le

end DomainTheory.Neighborhood
