/-ai
For neighbourhoods X and Y, the intersection of their brackets is nonempty if and only if some neighbourhood is contained in X ∩ Y.

If an element contains both neighbourhoods, their intersection belongs to the element and is therefore a neighbourhood, and it is contained in itself. Conversely, if a neighbourhood Z is contained in the intersection, the principal filter of Z contains both X and Y, because Z is contained in each of them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem110.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Theorem 1.10 (2).** `X, Y` are consistent in `𝒟` (have a common lower bound `Z ∈ 𝒟`,
`Z ⊆ X ∩ Y`) iff `[X] ∩ [Y] ≠ ∅`. `→` uses `↑Z` (which lies in both `[X]` and `[Y]`); `←` reads a
witness off any common element. -/
theorem bracket_inter_nonempty_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    (V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  constructor
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨X ∩ Y, x.sub (x.inter_mem hxX hxY), subset_rfl⟩
  · rintro ⟨Z, hZ, hZsub⟩
    refine ⟨V.principal hZ, ?_, ?_⟩
    · exact ⟨hX, hZsub.trans Set.inter_subset_left⟩
    · exact ⟨hY, hZsub.trans Set.inter_subset_right⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
