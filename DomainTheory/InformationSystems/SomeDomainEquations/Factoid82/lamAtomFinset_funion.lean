/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)






































































theorem lamAtomFinset_funion (u v : Finset (RawLamToken α)) :
    lamAtomFinset (u ∪' v) = lamAtomFinset u ∪' lamAtomFinset v := by
  ext x
  constructor
  · intro hx
    have : .atom x ∈ u ∪' v := mem_lamAtomFinset.1 hx
    rcases mem_funion.1 this with hu | hv
    · exact mem_funion.2 (Or.inl (mem_lamAtomFinset.2 hu))
    · exact mem_funion.2 (Or.inr (mem_lamAtomFinset.2 hv))
  · intro hx
    rcases mem_funion.1 hx with hu | hv
    · exact mem_lamAtomFinset.2 (mem_funion.2 (Or.inl (mem_lamAtomFinset.1 hu)))
    · exact mem_lamAtomFinset.2 (mem_funion.2 (Or.inr (mem_lamAtomFinset.1 hv)))

end InfoSys
end DomainTheory.InformationSystems
