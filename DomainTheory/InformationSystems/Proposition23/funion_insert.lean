/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Constructive
public import DomainTheory.InformationSystems.Definition22
public import DomainTheory.InformationSystems.Proposition23.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- `u ∪' insert a t = insert a (u ∪' t)`. -/
theorem funion_insert (u : Finset α) (a : α) (t : Finset α) :
    u ∪' insert a t = insert a (u ∪' t) := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with hu | hins
    · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inl hu))
    · rcases Finset.mem_insert.mp hins with ha | ht
      · exact Finset.mem_insert.mpr (Or.inl ha)
      · exact Finset.mem_insert_of_mem (mem_funion.mpr (Or.inr ht))
  · intro hx
    rcases Finset.mem_insert.mp hx with ha | h
    · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl ha)))
    · rcases mem_funion.mp h with hu | ht
      · exact mem_funion.mpr (Or.inl hu)
      · exact mem_funion.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr ht)))

end InfoSys
end DomainTheory.InformationSystems
