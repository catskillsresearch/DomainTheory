module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Cons law for the finite union of down-sets: `⋃_{X ∈ Y::L} ↓X = ↓Y ∪ ⋃_{X ∈ L} ↓X`. -/
theorem upSetUnion_cons (Y : Set α) (L : List (Set α)) :
    (⋃ X ∈ (Y :: L), V.upSet X) = V.upSet Y ∪ ⋃ X ∈ L, V.upSet X := by
  ext z
  rw [Set.mem_union, V.mem_PDunion, V.mem_PDunion]
  constructor
  · rintro ⟨X, hX, hz⟩
    rcases List.mem_cons.mp hX with rfl | hX'
    · exact Or.inl hz
    · exact Or.inr ⟨X, hX', hz⟩
  · rintro (hz | ⟨X, hX, hz⟩)
    · exact ⟨Y, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨X, List.mem_cons.mpr (Or.inr hX), hz⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
