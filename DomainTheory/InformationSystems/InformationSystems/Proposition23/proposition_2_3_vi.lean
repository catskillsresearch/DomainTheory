/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(vi).** `u ⊢ v` and `u ⊢ v'` imply `u ⊢ v ∪' v'`. -/
theorem proposition_2_3_vi {u v v' : Finset α}
    (huv : sys.EntSet u v) (huv' : sys.EntSet u v') : sys.EntSet u (v ∪' v') := by
  intro X hX
  rcases mem_funion.mp hX with h | h
  · exact huv X h
  · exact huv' X h

end InfoSys
end DomainTheory.InformationSystems
