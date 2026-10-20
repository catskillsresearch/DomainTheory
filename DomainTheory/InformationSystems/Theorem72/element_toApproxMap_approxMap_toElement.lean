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
public import DomainTheory.InformationSystems.Theorem72.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap











theorem element_toApproxMap_approxMap_toElement (f : ApproximableMap A B) :
    element_toApproxMap A B (approxMap_toElement A B f) = f := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨hu, hv, hp⟩
    change f.rel u v at hp
    exact hp
  · intro hrel
    exact ⟨f.rel_dom hrel, f.rel_cod hrel, by
      change f.rel u v
      exact hrel⟩

end InfoSys
end DomainTheory.InformationSystems
