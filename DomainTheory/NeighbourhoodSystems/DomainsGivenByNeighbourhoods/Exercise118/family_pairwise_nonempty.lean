/-ai
Every pair of members of the three-member family has nonempty intersection.

Membership in the family means each set is A, B, or Cc. The argument cases on those three choices for each member, and each of the nine intersections contains 0, 1, or 2.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118.Basic

@[expose] public section


set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- Every pair of members of `family` has non-empty intersection, hence (in the all-non-empty
system `triSys`) every pair is consistent. -/
theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩

end triSys
end DomainTheory.NeighbourhoodSystems
