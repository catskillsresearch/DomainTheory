/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition62
import DomainTheory.InformationSystems.Factoid32
import DomainTheory.InformationSystems.Theorem72.Basic
import DomainTheory.InformationSystems.Theorem72.mkFunToken_eq


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap











theorem approxMap_toElement_element_toApproxMap (x : (functionSystem A B).Element) :
    approxMap_toElement A B (element_toApproxMap A B x) = x := by
  apply le_antisymm
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2 at hp
    obtain ⟨_, _, hmem⟩ := hp
    simpa [mkFunToken_eq A B p] using hmem
  · intro p hp
    change (element_toApproxMap A B x).rel p.val.1 p.val.2
    refine ⟨p.property.1, p.property.2, ?_⟩
    simpa [mkFunToken_eq A B p] using hp

end InfoSys
end DomainTheory.InformationSystems
