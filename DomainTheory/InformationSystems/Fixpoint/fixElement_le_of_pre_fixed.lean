/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Factoid33
import DomainTheory.InformationSystems.Fixpoint.Basic
import DomainTheory.InformationSystems.Fixpoint.fixChain_subset_pre_fixed


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)














namespace ApproximableMap




/-- **Theorem 7.3(iii).** `fix(f)` is below every pre-fixed point. -/
theorem fixElement_le_of_pre_fixed (f : ApproximableMap A A) (x : A.Element)
    (hpre : f.toElement x ≤ x) : fixElement A f ≤ x := by
  intro a ⟨w, hw, ⟨hwCon, haCon, v0, hv0, hEnt⟩⟩
  obtain ⟨n, hn⟩ := hv0
  have hsub := fixChain_subset_pre_fixed A f x hpre hw hn
  have hEnta : A.Ent v0 a := hEnt a (Finset.mem_singleton_self _)
  exact x.closed v0 a hsub hEnta

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
