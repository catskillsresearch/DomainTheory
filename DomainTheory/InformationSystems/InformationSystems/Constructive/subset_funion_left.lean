/-ai
A finite set is contained in its choice-free union with any finite set.

A member of the first set is a left-hand member of the union by the membership law.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic

@[expose] public section


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]


theorem subset_funion_left (u v : Finset α) : u ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inl hx)

end DomainTheory.InformationSystems.Constructive
