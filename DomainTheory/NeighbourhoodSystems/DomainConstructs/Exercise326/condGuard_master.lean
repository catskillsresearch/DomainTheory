module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.zero_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.one_ne_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.condGuard

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

theorem condGuard_master {W : Set (Example12.Token ⊕ (α ⊕ α))} {Z : Set α} (hg : condGuard V W Z)
    (hC : Sum.inl ⁻¹' W = Example12.master) : V.master ⊆ Z := by
  rcases hg with ⟨hC', _⟩ | ⟨hC', _⟩ | ⟨_, h⟩
  · exact absurd (hC.symm.trans hC') zero_ne_master.symm
  · exact absurd (hC.symm.trans hC') one_ne_master.symm
  · exact h

end DomainTheory.NeighbourhoodSystems.Exercise326
