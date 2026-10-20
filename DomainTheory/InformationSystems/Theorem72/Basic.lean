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
public import DomainTheory.InformationSystems.Theorem72.approxMap_toElement
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap
public import DomainTheory.InformationSystems.Theorem72.applyMap
public import DomainTheory.InformationSystems.Theorem72.liftPair
public import DomainTheory.InformationSystems.Theorem72.curryMap
public import DomainTheory.InformationSystems.Theorem72.pairElements
public import DomainTheory.InformationSystems.Theorem72.uncurryMap
public import DomainTheory.InformationSystems.Theorem72.mkFunToken_property
public import DomainTheory.InformationSystems.Theorem72.funion_self
public import DomainTheory.InformationSystems.Theorem72.funion_comm_β
public import DomainTheory.InformationSystems.Theorem72.rel_input_output_union
public import DomainTheory.InformationSystems.Theorem72.funCon_of_approxMap
public import DomainTheory.InformationSystems.Theorem72.approxMap_toElement_consistent
public import DomainTheory.InformationSystems.Theorem72.approxMap_toElement_closed
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_rel_dom
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_rel_cod
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_empty_rel
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_union_right
public import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_mono
public import DomainTheory.InformationSystems.Theorem72.ProdCon_liftPair
public import DomainTheory.InformationSystems.Theorem72.fstFinset_liftPair
public import DomainTheory.InformationSystems.Theorem72.sndFinset_liftPair
public import DomainTheory.InformationSystems.Theorem72.entSet_liftPair
public import DomainTheory.InformationSystems.Theorem72.rel_of_funTokens
public import DomainTheory.InformationSystems.Theorem72.funCon_of_curry_pointwise

@[expose] public section

/-!
# Theorem 7.2 — function space elements, apply, and curry

**Scott 1982, Theorem 7.2.** Approximable maps `A → B` are exactly the elements of
`|A → B|`. There is approximable `apply : (B → C) × B → C` with `apply(g,y) = g(y)`,
and for each `h : A × B → C` a unique `curry h : A → (B → C)` satisfying
`h = apply ∘ ⟨(curry h) ∘ fst, snd⟩`.

(`A → B` as an `InfoSys` is already Def 7.1 / `functionSystem`.)
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap












/-! ## Curry helpers -/










end InfoSys
end DomainTheory.InformationSystems
