/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Approximable
import DomainTheory.InformationSystems.Proposition54.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


/-- **Proposition 5.4(ii).** `I_A(x) = x`. -/
theorem idMap_toElement (x : A.Element) : (idMap A).toElement x = x := by
  apply le_antisymm
  · intro Y ⟨u, hu, hrel⟩
    -- hrel.2.2 : EntSet u {Y}, so Ent u Y
    have hEnt : A.Ent u Y := hrel.2.2 Y (Finset.mem_singleton_self Y)
    exact x.closed u Y hu hEnt
  · intro Y hY
    refine ⟨{Y}, ?_, ?_⟩
    · intro z hz
      have hz' : z ∈ ({Y} : Finset α) := Finset.mem_coe.1 hz
      rw [Finset.mem_singleton] at hz'
      rw [hz']
      exact hY
    · refine ⟨A.con_sing Y, A.con_sing Y, ?_⟩
      exact proposition_2_3_iii A (A.con_sing Y)

end InfoSys
end DomainTheory.InformationSystems
