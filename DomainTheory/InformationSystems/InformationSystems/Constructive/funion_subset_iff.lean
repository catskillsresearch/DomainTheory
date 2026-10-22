/-ai
A choice-free union is contained in a finite set w if and only if both summands are contained in w.

If the union is contained in w, each summand is contained in the union and hence in w. If both summands are contained in w, a member of the union lies in one summand and hence in w.
ai-/
module

public import Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.subset_funion_left
public import DomainTheory.InformationSystems.InformationSystems.Constructive.subset_funion_right

@[expose] public section


namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]


/-- Universal property of the union: `u ∪' v ⊆ w` iff both `u ⊆ w` and `v ⊆ w`. -/
theorem funion_subset_iff {u v w : Finset α} : u ∪' v ⊆ w ↔ u ⊆ w ∧ v ⊆ w := by
  constructor
  · intro h
    exact ⟨fun x hx => h (subset_funion_left u v hx),
           fun x hx => h (subset_funion_right u v hx)⟩
  · rintro ⟨hu, hv⟩ x hx
    rcases mem_funion.1 hx with h | h
    exacts [hu h, hv h]

end DomainTheory.InformationSystems.Constructive
