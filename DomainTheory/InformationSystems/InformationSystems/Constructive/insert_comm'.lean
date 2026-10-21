/-ai
Inserting an element a and then an element b into a finite set equals inserting b and then a. This choice-free commutativity is what permits folding insertion over a multiset.

Extensionality is used. Membership is a three-way disjunction, and the two outer cases are exchanged while membership in the original set is left unchanged.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

/-- Choice-free commutativity of `insert` (mathlib's `Finset.insert_comm` is choice-tainted).
Needed to fold `insert` over a `Multiset`. -/
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
