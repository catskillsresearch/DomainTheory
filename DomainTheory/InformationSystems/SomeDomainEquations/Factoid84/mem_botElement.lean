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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84









theorem mem_botElement (x : ℕ) : x ∈ botElement.carrier ↔ x = 0 := by
  constructor
  · intro hx
    have : PEnt ∅ x := (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · rfl
    · exact False.elim (Finset.notMem_empty _ hx')
  · rintro rfl
    exact (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).2 (Or.inl rfl)

end Factoid84
end DomainTheory.InformationSystems
