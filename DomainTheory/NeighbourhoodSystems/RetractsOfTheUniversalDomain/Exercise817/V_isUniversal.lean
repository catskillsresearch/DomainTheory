/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.U_isUniversal
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.isUniversal_of_isomorphic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}











/-- **Exercise 8.17, Part 3.** Exercise 8.12's `V` (a `NeighborhoodSystem ℕ`, built from `2^kℕ+ℓ` —
literally a *different* neighbourhood system from `U : NeighborhoodSystem ℚ`, not merely a
relabelling) is a universal domain, since it is effectively isomorphic to `𝒰` (`effectiveIso812_UV`,
Exercise 8.12's headline) and universality transports along isomorphism. -/
theorem V_isUniversal : IsUniversal.{u} V :=
  isUniversal_of_isomorphic U_isUniversal ⟨effectiveIso812_UV.toDomainIso⟩

end DomainTheory.NeighbourhoodSystems
