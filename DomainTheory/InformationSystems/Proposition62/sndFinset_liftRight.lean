/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Product
import DomainTheory.InformationSystems.Proposition53
import DomainTheory.InformationSystems.Proposition55
import DomainTheory.InformationSystems.Proposition62.Basic
import DomainTheory.InformationSystems.Proposition62.mem_liftRight


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem sndFinset_liftRight (w : Finset β) : sndFinset A B (liftRight A B w) = w := by
  ext y
  constructor
  · intro hy
    rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
    rcases (mem_liftRight A B).1 hp with ⟨z, hz, hp'⟩
    subst hp'
    exact (show z = y from hy').symm ▸ hz
  · intro hy
    exact (mem_sndFinset A B).2
      ⟨mkRight A B y, (mem_liftRight A B).2 ⟨y, hy, rfl⟩, rfl, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
