/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Proposition23
import DomainTheory.InformationSystems.FunctionSpace.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]



variable (A : InfoSys α) (B : InfoSys β)

















theorem funInputUnion_empty : funInputUnion A B (∅ : Finset (FunToken A B)) = ∅ :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
