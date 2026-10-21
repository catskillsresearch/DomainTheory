/-ai
The token system is positive: the intersection of two of its neighbourhoods is a neighbourhood if and only if the intersection is nonempty.

The intersection of the brackets of two neighbourhoods is the bracket of their intersection. If that bracket equals the bracket of some neighbourhood, the principal filter of the neighbourhood lies in it. Conversely, an element of the bracket contains the intersection, so the intersection is a neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.21 — the token system is positive.** `[X] ∩ [Y] = [X ∩ Y]` is a neighbourhood
iff non-empty: a common element `x` gives `X ∩ Y ∈ 𝒟` (via `x.sub (x.inter_mem …)`); conversely
`[W]` always contains the principal filter `↑W`. -/
theorem tokenSystem_isPositive : V.tokenSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.bracket_inter hX hY]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨V.principal hW, V.principal_mem_bracket hW⟩
  · rintro ⟨x, hx⟩
    exact ⟨X ∩ Y, x.sub hx, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
