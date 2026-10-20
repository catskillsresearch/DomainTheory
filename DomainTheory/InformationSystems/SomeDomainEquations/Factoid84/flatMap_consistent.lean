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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_consistent : ConsistentApprox flatMap := by
  intro hsub
  have h1 : 1 ∈ (barElement 1).carrier := (mem_barElement 1 1).2 (Or.inr rfl)
  have h1' : 1 ∈ (flatMap.toElement (barElement 0)).carrier := hsub h1
  rcases (mem_toElement flatMap (barElement 0)).1 h1' with ⟨u, hu, hrel⟩
  rcases hrel with h1u | ⟨_, hv1⟩
  · have : 1 ∈ (barElement 0).carrier := hu (Finset.mem_coe.2 h1u)
    rcases (mem_barElement 0 1).1 this with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact hv1 (Finset.mem_singleton_self 1)

end Factoid84

end DomainTheory.InformationSystems
