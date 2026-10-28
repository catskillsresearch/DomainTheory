module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Injective.InjectiveSpace
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

public import DomainTheory.ContinuousLattice.ContinuousLattices.theorem_2_12_more

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

/-- **Scott 1972, Theorem 2.12.** A `T₀`-space is injective iff it is (homeomorphic to) a
continuous lattice under its Scott topology. The forward direction is Proposition 2.11; the
backward direction is `theorem_2_12.backward`. -/
theorem theorem_2_12 {D : Type u} [TopologicalSpace D] [T0Space D] :
    InjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @ContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  refine ⟨theorem_2_12.backward, ?_⟩
  rintro ⟨E, inst, hE, ⟨h⟩⟩
  let τE : TopologicalSpace E := @scottTopologicalSpace E inst
  exact @InjectiveSpace.of_retract E D τE _ (theorem_2_12.forward hE)
    ⟨⇑h, h.continuous⟩ ⟨⇑h.symm, h.symm.continuous⟩ (fun d => h.left_inv d)

end DomainTheory.ContinuousLattice
