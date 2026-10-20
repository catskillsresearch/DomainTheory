/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid36.Basic
import DomainTheory.InformationSystems.Factoid36.closure_le_of_subset


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- The family of finite approximations to `x` is directed under `≤`. -/
theorem closures_directed (x : sys.Element) {u v : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huX : ↑u ⊆ x.carrier) (hvX : ↑v ⊆ x.carrier) :
    ∃ (w : Finset α) (hw : w ∈ sys.Con),
      ↑w ⊆ x.carrier ∧
        sys.closure u hu ≤ sys.closure w hw ∧
        sys.closure v hv ≤ sys.closure w hw := by
  let w := u ∪' v
  have hwX : ↑w ⊆ x.carrier := by
    intro a ha
    rcases mem_funion.1 (Finset.mem_coe.1 ha) with h | h
    · exact huX (Finset.mem_coe.2 h)
    · exact hvX (Finset.mem_coe.2 h)
  have hw : w ∈ sys.Con := x.consistent w hwX
  refine ⟨w, hw, hwX, ?_, ?_⟩
  · exact sys.closure_le_of_subset hu hw (subset_funion_left u v)
  · exact sys.closure_le_of_subset hv hw (subset_funion_right u v)

end InfoSys
end DomainTheory.InformationSystems
