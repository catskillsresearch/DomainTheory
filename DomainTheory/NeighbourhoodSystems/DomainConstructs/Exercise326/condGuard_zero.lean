/-ai
If the conditional guard holds and the truth component is the singleton of zero, the left value component is contained in the output.

The one clause would identify that singleton with the singleton of one, and the master clause would identify it with the master. The remaining clause is the left-hand inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_one
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

theorem condGuard_zero {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.zero) : Sum.inl ⁻¹' (Sum.inr ⁻¹' W) ⊆ Z := by
  rcases hg with ⟨_, h⟩ | ⟨hC', _⟩ | ⟨hC', _⟩
  · exact h
  · exact absurd (hC.symm.trans hC') zero_ne_one
  · exact absurd (hC.symm.trans hC') zero_ne_master

end DomainTheory.NeighbourhoodSystems.Exercise326
