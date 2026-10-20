module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic

@[expose] public section


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]







/-- The coercion of `u ∪' v` to a `Set` is the (choice-free) set union of the coercions. -/
theorem coe_funion (u v : Finset α) :
    (↑(u ∪' v) : Set α) = (↑u : Set α) ∪ ↑v := by
  ext x
  simp only [Set.mem_union, Finset.mem_coe, mem_funion]

end DomainTheory.InformationSystems.Constructive
