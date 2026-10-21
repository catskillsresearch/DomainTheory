/-ai
Constructive union on the left distributes over insertion: the constructive union of u with the insertion of a into t equals the insertion of a into the constructive union of u with t.

Both inclusions are membership chasing. A member of the left-hand union comes from u, hence lies in the inserted union, or comes from the inserted set, hence is a or a member of t, and in each case lies in the inserted union. A member of the inserted union is a, which lies on the inserted side of the original union, or a member of the constructive union, which comes from u or from t and is reassembled on the left.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.Basic

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
