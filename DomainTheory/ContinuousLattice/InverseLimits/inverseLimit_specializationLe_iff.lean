/-ai
The specialization order of the subspace inverse-limit topology is the componentwise order.

The inclusion of the inverse limit into the product is a topological embedding. Specialization is the specializes relation, which transfers along that embedding and splits over the product. At each coordinate, specializes agrees with the specialization order of the Scott topology, which is the lattice order.
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


/-- The specialization order of the explicit inverse-limit topology is the componentwise order. -/
theorem inverseLimit_specializationLe_iff (x y : InverseLimit D P) :
    @SpecializationLe (InverseLimit D P) (inverseLimitTopology D P) x y ↔ x ≤ y := by
  let stageOrder : ∀ n, Preorder (D n) := fun _ => inferInstance
  let limitOrder : Preorder (InverseLimit D P) := inferInstance
  let : ∀ n, TopologicalSpace (D n) := fun _ => scottTopologicalSpace
  let : TopologicalSpace (InverseLimit D P) := inverseLimitTopology D P
  let : ∀ n, Preorder (D n) := stageOrder
  let : Preorder (InverseLimit D P) := limitOrder
  have hval : Topology.IsEmbedding (Subtype.val : InverseLimit D P → ∀ n, D n) :=
    ⟨⟨rfl⟩, Subtype.val_injective⟩
  rw [specializationLe_iff_specializes, ← hval.isInducing.specializes_iff, specializes_pi]
  constructor
  · intro h n
    rw [← specializationLe_scott_iff, specializationLe_iff_specializes]
    exact h n
  · intro h n
    rw [← specializationLe_iff_specializes, specializationLe_scott_iff]
    exact h n

end InverseLimit
end DomainTheory.ContinuousLattice
