/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Constructive
import DomainTheory.InformationSystems.Factoid35
import DomainTheory.InformationSystems.Factoid42
import DomainTheory.InformationSystems.Factoid43.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




theorem subset_deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) :
    U ⊆ (sys.deductiveClosure U hU).carrier := by
  intro a ha
  refine ⟨{a}, ?_, sys.ent_refl (hU {a} ?_) (Finset.mem_singleton_self a)⟩
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha

end InfoSys
end DomainTheory.InformationSystems
