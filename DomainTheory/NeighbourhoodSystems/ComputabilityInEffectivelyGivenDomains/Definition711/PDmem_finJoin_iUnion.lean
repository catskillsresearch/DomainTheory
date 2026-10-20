module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition711.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)









/-- **Definition 7.11 — Scott's displayed union form.** For `n ≥ 1`, membership is equivalent to
some representatives `X_i ∈ x_i` with `⋃_{i<n} ↓X_i ⊆ W`. -/
theorem PDmem_finJoin_iUnion {m : ℕ} (xs : Fin (m + 1) → V.Element) {W : Set (Set α)} :
    (V.PDfinJoinSucc xs).mem W ↔
      ∃ (X : Fin (m + 1) → Set α) (_hX : ∀ i, (xs i).mem (X i)),
        V.PowerDomain.mem W ∧
          (⋃ i, V.upSet (X i)) ⊆ W := by
  rw [PDmem_finJoinSucc]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X, hX, hPD, Set.iUnion_subset hsub⟩
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨X, hX, hPD, (Set.iUnion_subset_iff).mp hsub⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
