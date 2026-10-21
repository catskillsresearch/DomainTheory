/-ai
B is a literal subsystem of C: the two systems have the same master, every B-neighbourhood is a C-neighbourhood, and the intersection of two B-neighbourhoods is a B-neighbourhood whenever it is a C-neighbourhood.

The masters agree by reflexivity. A B-neighbourhood is the cone of a string, hence a C-neighbourhood. For the intersection, trichotomy of cones gives nesting one way, nesting the other way, or disjointness. In the nested cases the intersection is the smaller cone. In the disjoint case the intersection is empty, which cannot be a C-neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822



/-- **`B` is a literal subsystem of `C`** (Definition 6.10): every `B`-neighbourhood is already a
`C`-neighbourhood, and consistency is inherited — if two cones intersect to a `C`-neighbourhood
(hence nonempty), `cone_trichotomy` rules out the disjoint case, so the intersection is already the
smaller of the two cones. -/
theorem B_subsystem_C : B ◁ C where
  master_eq := rfl
  sub := by rintro X ⟨σ, rfl⟩; exact memC_cone σ
  inter_closed := by
    rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩ hCXY
    rcases cone_trichotomy σ τ with h | h | h
    · rw [Set.inter_eq_left.mpr h]; exact ⟨σ, rfl⟩
    · rw [Set.inter_eq_right.mpr h]; exact ⟨τ, rfl⟩
    · rw [h] at hCXY; exact absurd (C_nonempty ∅ hCXY) (by simp)

end Exercise822
end DomainTheory.NeighbourhoodSystems
