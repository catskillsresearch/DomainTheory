/-ai
Scott 1972, Theorem 2.12. A T₀-space is injective if and only if it is homeomorphic to a continuous lattice carrying its Scott topology.

The direction from injectivity is the backward half of the theorem. In the other direction, the homeomorphism exhibits the space as a retract of the continuous lattice. A continuous lattice is injective, and a retract of an injective space is injective.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic
public import DomainTheory.ContinuousLattice.Theorem212.theorem_2_12_backward

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set



universe u

/-- **Scott 1972, Theorem 2.12.** A `T₀`-space is injective iff it is (homeomorphic to) a
continuous lattice under its Scott topology. The forward direction is Proposition 2.11; the
backward direction is `theorem_2_12_backward`. -/
theorem theorem_2_12 {D : Type u} [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @IsContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  refine ⟨theorem_2_12_backward, ?_⟩
  rintro ⟨E, inst, hE, ⟨h⟩⟩
  let τE : TopologicalSpace E := @scottTopologicalSpace E inst
  exact @IsInjectiveSpace.of_retract E D τE _ (theorem_2_12_forward hE)
    ⟨⇑h, h.continuous⟩ ⟨⇑h.symm, h.symm.continuous⟩ (fun d => h.left_inv d)

end DomainTheory.ContinuousLattice
