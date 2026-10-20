/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Factoid36
import DomainTheory.InformationSystems.Factoid44
import DomainTheory.InformationSystems.Factoid45.Basic
import DomainTheory.InformationSystems.Factoid45.botElement_eq_closure_empty


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


theorem nonempty_finiteApproximants (x : sys.Element) :
    (sys.finiteApproximants x).Nonempty := by
  refine ⟨sys.botElement, ∅, sys.con_empty, ?_, sys.botElement_eq_closure_empty⟩
  intro a ha
  exact False.elim (Finset.notMem_empty _ (Finset.mem_coe.1 ha))

end InfoSys
end DomainTheory.InformationSystems
