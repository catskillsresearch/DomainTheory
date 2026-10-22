module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic

@[expose] public section


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]


theorem subset_funion_right (u v : Finset α) : v ⊆ u ∪' v := fun _ hx => mem_funion.2 (Or.inr hx)

end DomainTheory.InformationSystems.Constructive
