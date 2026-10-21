/-ai
An element belongs to a choice-free union of finite sets if and only if it belongs to one of the two sets.

The proof is the membership law for a fold of insertion, applied to the underlying multiset of the second set.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.instLeftCommutativeInsert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.mem_foldr_insert
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic.notation5

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

@[simp] theorem mem_funion {a : α} {u v : Finset α} :
    a ∈ u ∪' v ↔ a ∈ u ∨ a ∈ v := mem_foldr_insert a u v.1

end DomainTheory.InformationSystems.Constructive
