/-ai
The truth component and the two value components of an input neighbourhood of the conditional are themselves neighbourhoods.

Such a neighbourhood is a product of a truth neighbourhood with a product of two neighbourhoods, and the three preimages recover those three neighbourhoods.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.TD

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

variable (V : NeighborhoodSystem α)

/-- The three components `C, X, Y` of an input neighbourhood are themselves neighbourhoods. -/
theorem cond_components {W : Set (Example12.Token ⊕ (α ⊕ α))}
    (hW : (prod TD (prod V V)).mem W) :
    Example12.mem (Sum.inl ⁻¹' W) ∧
      V.mem (Sum.inl ⁻¹' (Sum.inr ⁻¹' W)) ∧ V.mem (Sum.inr ⁻¹' (Sum.inr ⁻¹' W)) := by
  obtain ⟨C, P, hC, hP, rfl⟩ := hW
  obtain ⟨X, Y, hX, hY, rfl⟩ := hP
  simp only [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨hC, hX, hY⟩

end DomainTheory.NeighbourhoodSystems.Exercise326
