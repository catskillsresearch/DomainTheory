module

public import DomainTheory.ContinuousLattice.InverseLimits.inverseLimitTopology
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- Every coordinate projection from the explicit product/subspace inverse-limit topology is
continuous. -/
theorem inverseLimit_coordinate_continuous (n : ℕ) :
    @Continuous (InverseLimit D P) (D n) (inverseLimitTopology D P)
      scottTopologicalSpace (fun x => x.1 n) := by
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  rw [continuous_def]
  intro U hU
  rw [isOpen_induced_iff]
  exact ⟨{x : ∀ n, D n | x n ∈ U},
    (@continuous_apply ℕ D (fun _ => scottTopologicalSpace) n).isOpen_preimage U hU, rfl⟩

end InverseLimit
end DomainTheory.ContinuousLattice
