module

public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

theorem insert_comm' (a b : α) (s : Finset α) :
    insert a (insert b s) = insert b (insert a s) := by
  ext x
  simp only [Finset.mem_insert]
  constructor
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]
  · rintro (h | h | h)
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr h)]

end DomainTheory.InformationSystems.Constructive
