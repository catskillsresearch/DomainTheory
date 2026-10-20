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

theorem lamOutputUnion_funion
    (s t : Finset (List (RawLamToken α) × List (RawLamToken α))) :
    lamOutputUnion (s ∪' t) = lamOutputUnion s ∪' lamOutputUnion t := by
  ext x
  constructor
  · intro hx
    rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
    rcases mem_funion.1 hp with hp | hp
    · exact mem_funion.2 (Or.inl ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
    · exact mem_funion.2 (Or.inr ((mem_lamOutputUnion).2 ⟨p, hp, hx'⟩))
  · intro hx
    rcases mem_funion.1 hx with hx | hx
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inl hp), hx'⟩
    · rcases (mem_lamOutputUnion).1 hx with ⟨p, hp, hx'⟩
      exact (mem_lamOutputUnion).2 ⟨p, mem_funion.2 (Or.inr hp), hx'⟩

end InfoSys

end DomainTheory.InformationSystems
