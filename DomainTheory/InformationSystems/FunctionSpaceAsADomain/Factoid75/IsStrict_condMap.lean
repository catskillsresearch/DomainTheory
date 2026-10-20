/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem IsStrict_condMap (x y : A.Element) : IsStrict boolSystem A (condMap A x y) := by
  apply le_antisymm
  · intro Z ⟨u, hu, ⟨_, _, hE, _, _⟩⟩
    have hEmp : EmptyEntails boolSystem u := fun t ht =>
      mem_botElement_emptyEntails boolSystem (hu (Finset.mem_coe.2 ht))
    exact emptyEntails_mem_botElement A (hE hEmp Z (Finset.mem_singleton_self _))
  · exact botElement_le A _

end InfoSys

end DomainTheory.InformationSystems
