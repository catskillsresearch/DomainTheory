/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

/-- If `1 ∈ u`, accept any `v`; else require `v ⊆ u ∪ {0}` and `1 ∉ v`. -/
def flatRel (u v : Finset ℕ) : Prop :=
  (1 ∈ u) ∨ ((∀ n ∈ v, n = 0 ∨ n ∈ u) ∧ 1 ∉ v)

end Factoid84

end DomainTheory.InformationSystems
