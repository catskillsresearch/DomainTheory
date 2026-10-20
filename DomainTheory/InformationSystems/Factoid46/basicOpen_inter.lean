/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Approximable
import DomainTheory.InformationSystems.Factoid45
import DomainTheory.InformationSystems.Factoid46.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


/-- Intersection of basic opens: `[u] ∩ [v] = [u ∪' v]`. -/
theorem basicOpen_inter (A : InfoSys α) (u v : Finset α) :
    A.basicOpen u ∩ A.basicOpen v = A.basicOpen (u ∪' v) := by
  ext x
  constructor
  · intro ⟨hu, hv⟩ a ha
    rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
    · exact hu (Finset.mem_coe.2 h)
    · exact hv (Finset.mem_coe.2 h)
  · intro huv
    refine ⟨?_, ?_⟩
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inl (Finset.mem_coe.1 ha))))
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inr (Finset.mem_coe.1 ha))))

end InfoSys
end DomainTheory.InformationSystems
