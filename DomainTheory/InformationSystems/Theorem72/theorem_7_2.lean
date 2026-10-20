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
import DomainTheory.InformationSystems.Theorem72.element_toApproxMap_approxMap_toElement
import DomainTheory.InformationSystems.Theorem72.approxMap_toElement_element_toApproxMap


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)






open ApproximableMap























/-- **Theorem 7.2, first sentence (Scott 1982).** Approximable maps `A → B` are
exactly the elements of the Definition 7.1 function-space system `|A → B|`.
The `apply` / `curry` clauses of the same numbered theorem are proved above
and are not this compared declaration. -/
theorem theorem_7_2 {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    (∀ f : ApproximableMap A B,
      element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
    (∀ x : (functionSystem A B).Element,
      approxMap_toElement A B (element_toApproxMap A B x) = x) :=
  ⟨element_toApproxMap_approxMap_toElement A B,
    approxMap_toElement_element_toApproxMap A B⟩

end InfoSys
end DomainTheory.InformationSystems
