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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem lamFunFinset_funion (u v : Finset (RawLamToken α)) :
    lamFunFinset (u ∪' v) = lamFunFinset u ∪' lamFunFinset v := by
  ext p
  constructor
  · intro hp
    have : .funTok p.1 p.2 ∈ u ∪' v := mem_lamFunFinset.1 hp
    rcases mem_funion.1 this with hu | hv
    · exact mem_funion.2 (Or.inl (mem_lamFunFinset.2 hu))
    · exact mem_funion.2 (Or.inr (mem_lamFunFinset.2 hv))
  · intro hp
    rcases mem_funion.1 hp with hu | hv
    · exact mem_lamFunFinset.2 (mem_funion.2 (Or.inl (mem_lamFunFinset.1 hu)))
    · exact mem_lamFunFinset.2 (mem_funion.2 (Or.inr (mem_lamFunFinset.1 hv)))

end InfoSys

end DomainTheory.InformationSystems
