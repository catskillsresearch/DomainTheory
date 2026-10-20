/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Proposition53
public import DomainTheory.InformationSystems.Proposition55
public import DomainTheory.InformationSystems.Proposition62.Basic
public import DomainTheory.InformationSystems.Proposition62.mem_liftLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)








theorem sndFinset_liftLeft (v : Finset α) :
    sndFinset A B (liftLeft A B v) ⊆ ({B.bot} : Finset β) := by
  intro y hy
  rcases (mem_sndFinset A B).1 hy with ⟨p, hp, hbot, hy'⟩
  rcases (mem_liftLeft A B).1 hp with ⟨x, _, hp'⟩
  subst hp'
  -- mkLeft x has first component x; filter requires x = A.bot, and second is B.bot
  have : y = B.bot := hy'.symm
  exact Finset.mem_singleton.mpr this

end InfoSys
end DomainTheory.InformationSystems
