/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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

/-- `which(in₀ x) ≤ true`: a left-injected element's tag never reaches `false`. -/
theorem which_inMap₀_le_trueElt (x : V₀.Element) :
    (whichMap V₀ V₁ h₀ h₁).toElementMap ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)
      ≤ Example23.trueElt := by
  intro Z hZ
  rcases (Example12.mem_iff Z).mp
      (((whichMap V₀ V₁ h₀ h₁).toElementMap
        ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap x)).sub hZ) with rfl | rfl | rfl
  · exact Example23.trueElt.master_mem
  · show Example23.trueElt.mem Example12.zero
    exact Or.inr rfl
  · exfalso
    obtain ⟨Y, hY, hmem⟩ := which_mem_one.mp hZ
    obtain ⟨X, _, hX0, _, hsub⟩ := hmem
    exact not_inj₀_subset_inj₁ (h₀ X hX0) hsub

end SumHelpers
end DomainTheory.NeighbourhoodSystems
