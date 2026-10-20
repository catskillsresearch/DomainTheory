/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Definition22.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

universe u

variable {α : Type u} [DecidableEq α] (sys : InfoSys α)


theorem entSet_empty (u : Finset α) : sys.EntSet u (∅ : Finset α) := by
  intro X hX
  exact False.elim (Finset.notMem_empty X hX)

end InfoSys
end DomainTheory.InformationSystems
