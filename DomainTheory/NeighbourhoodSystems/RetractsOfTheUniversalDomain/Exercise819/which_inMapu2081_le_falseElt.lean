/-ai
The tag of a right injection lies below the element false. A right-injected element never receives the tag true.

A neighbourhood of the tag is one of the three neighbourhoods of the three-point domain. The master belongs to false, and the one neighbourhood is the neighbourhood of false. The zero neighbourhood cannot occur, because it would require a right injection to be contained in a left injection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- `which(in₁ y) ≤ false`: a right-injected element's tag never reaches `true`. -/
theorem which_inMap₁_le_falseElt (y : V₁.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)
      ≤ Example23.falseElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap y)).sub hZ) with rfl | rfl | rfl
  · exact Example23.falseElt.master_mem
  · exfalso
    obtain ⟨X, hX, hmem⟩ := which_mem_zero.mp hZ
    obtain ⟨Y, _, hY0, _, hsub⟩ := hmem
    exact not_inj₁_subset_inj₀ (h₁ Y hY0) hsub
  · show Example23.falseElt.mem Example12.one
    exact Or.inr rfl

end SumHelpers
end DomainTheory.NeighbourhoodSystems
