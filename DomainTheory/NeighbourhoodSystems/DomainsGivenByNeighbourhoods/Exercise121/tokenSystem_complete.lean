/-ai
The token system is complete. Every filter is fixed by the element whose neighbourhoods are those whose brackets belong to the filter, and by no other element.

A neighbourhood of the token system is a bracket of some neighbourhood, and that bracket belongs to the filter if and only if the recovered element lies in the bracket. If another element fixes the same filter, the two elements contain the same sets: when the set is a neighbourhood, the fixing property at its bracket transfers membership either way, and when the set is not a neighbourhood, neither element contains it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)



/-- **Exercise 1.21 — the token system is complete.** Every filter `y` of `{[X]}` is fixed by
the unique point `ofToken y ∈ |𝒟|`: `[W] ∈ y ↔ ofToken y ∈ [W]`. Uniqueness is `Element.ext`
applied through the brackets. -/
theorem tokenSystem_complete : V.tokenSystem.IsComplete := by
  intro y
  refine ⟨V.ofToken y, ?_, ?_⟩
  · rintro S ⟨W, hW, rfl⟩
    constructor
    · intro hyW; exact ⟨hW, hyW⟩
    · rintro ⟨_, hyW⟩; exact hyW
  · intro b hb
    apply Element.ext
    intro W
    by_cases hW : V.mem W
    · have hb' := hb (V.bracket W) ⟨W, hW, rfl⟩
      constructor
      · intro hbW; exact ⟨hW, hb'.mpr hbW⟩
      · intro hxW; exact hb'.mp hxW.2
    · constructor
      · intro hbW; exact absurd (b.sub hbW) hW
      · intro hxW; exact absurd ((V.ofToken y).sub hxW) hW

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
