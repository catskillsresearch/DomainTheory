/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpace
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62
public import DomainTheory.InformationSystems.Factoid32
public import DomainTheory.InformationSystems.Theorem72.mkFunToken
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_rel_dom
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_rel_cod
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_empty_rel
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_union_right
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

/-- **Theorem 7.2.** Element of `|A → B|` as an approximable map. -/
def element_toApproxMap (x : (functionSystem A B).Element) : ApproximableMap A B where
  rel u v := ∃ (hu : u ∈ A.Con) (hv : v ∈ B.Con), mkFunToken A B u v hu hv ∈ x.carrier
  rel_dom := element_toApproxMap_rel_dom A B x
  rel_cod := element_toApproxMap_rel_cod A B x
  empty_rel := element_toApproxMap_empty_rel A B x
  union_right := element_toApproxMap_union_right A B x
  mono := element_toApproxMap_mono A B x

end InfoSys

end DomainTheory.InformationSystems
