module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_nil
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.enc_cons
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_mem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822.D'_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB Example44 Example62

namespace Exercise822

/-- **`D' ◁ B`.** Same master; `D'.mem ⊆ B.mem` since every `D'`-set is a `B`-cone; and
consistency is inherited via `D'_nestedOrDisjoint` exactly as in `B_subsystem_C`. -/
theorem D'_subsystem_B : D' ◁ B where
  master_eq := rfl
  sub := by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact ⟨_, rfl⟩
  inter_closed := by
    rintro X Y hX hY hBXY
    rcases D'_nestedOrDisjoint hX hY with h | h | h
    · rw [Set.inter_eq_left.mpr h]; exact hX
    · rw [Set.inter_eq_right.mpr h]; exact hY
    · rw [h] at hBXY; exact absurd (B_nonempty ∅ hBXY) (by simp)

end Exercise822

end DomainTheory.NeighbourhoodSystems
