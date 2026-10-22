/-ai
This instance registers left commutativity of insertion of an element into a finite set. The witness is the choice-free commutativity of insertion.
ai-/
module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.insert_comm'

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

instance instLeftCommutativeInsert :
    LeftCommutative (insert : α → Finset α → Finset α) := ⟨insert_comm'⟩

end DomainTheory.InformationSystems.Constructive
