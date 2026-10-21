/-ai
The bracket of a set is nonempty if and only if the set is a neighbourhood.

An element of the bracket contains the set, so the set is a neighbourhood. Conversely, the principal filter of a neighbourhood lies in the bracket of that neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise121.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)





/-- `[X] ≠ ∅ ⟺ X ∈ 𝒟`. `→` reads `X ∈ 𝒟` off any element of `[X]`; `←` exhibits `↑X`. -/
theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
