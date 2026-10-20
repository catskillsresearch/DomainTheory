/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 3.2.** Every element contains `Δ`. -/
theorem factoid_3_2 (x : sys.Element) : sys.bot ∈ x.carrier := by
  have hempty : (↑(∅ : Finset α) : Set α) ⊆ x.carrier := by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))
  have hEnt : sys.Ent ∅ sys.bot := sys.ent_bot sys.con_empty
  exact x.closed ∅ sys.bot hempty hEnt

end InfoSys
end DomainTheory.InformationSystems
