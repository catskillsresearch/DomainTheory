/-ai
Every coordinate projection is continuous from the subspace inverse-limit topology into the Scott topology of that stage.

For an open set U of the stage, its preimage under the coordinate is the preimage, under the inclusion into the product, of the set of tuples whose corresponding coordinate lies in U. That set of tuples is open because evaluation at the coordinate is continuous on the product.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic

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
