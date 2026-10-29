module

public import DomainTheory.ContinuousLattice.Constructions.proposition_2_11
public import DomainTheory.ContinuousLattice.ContinuousLattices.injective_homeomorph_to_continuousLatticeScott
public import DomainTheory.ContinuousLattice.Injective.proposition_1_4

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

theorem theorem_2_12 {D : Type u} [TopologicalSpace D] [T0Space D] :
    InjectiveSpace.{u, u} D ↔
      ∃ (E : Type u) (inst : CompleteLattice E),
        @ContinuousLattice E inst ∧
          Nonempty (@Homeomorph D E _ (@scottTopologicalSpace E inst)) := by
  refine ⟨injective_homeomorph_to_continuousLatticeScott, ?_⟩
  rintro ⟨E, inst, hE, ⟨h⟩⟩
  let τE : TopologicalSpace E := @scottTopologicalSpace E inst
  exact @proposition_1_4 E D τE _ (proposition_2_11 hE)
    ⟨⇑h, h.continuous⟩ ⟨⇑h.symm, h.symm.continuous⟩ (fun d => h.left_inv d)

end DomainTheory.ContinuousLattice
