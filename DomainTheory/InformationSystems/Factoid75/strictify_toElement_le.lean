/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Multiset.MapFold
import DomainTheory.InformationSystems.FunctionSpace
import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid25
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid75.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap



theorem strictify_toElement_le (f : ApproximableMap A B) (x : A.Element) :
    (strictify A B f).toElement x ≤ f.toElement x := by
  intro Z ⟨u, hu, ⟨_, _, hcase⟩⟩
  rcases hcase with hE | ⟨hf, _⟩
  · exact (botElement_le B (f.toElement x))
      (emptyEntails_mem_botElement B (hE Z (Finset.mem_singleton_self _)))
  · exact ⟨u, hu, hf⟩

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
