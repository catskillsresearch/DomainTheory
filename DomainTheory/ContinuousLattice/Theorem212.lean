/-ai
Scott 1972, Theorem 2.12. A T₀-space is injective if and only if it is homeomorphic to a continuous lattice carrying its Scott topology.

The numbered name theorem_212 is that statement.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212.theorem_2_12

@[expose] public section

namespace DomainTheory.ContinuousLattice

set_option linter.unusedVariables false

theorem theorem_212.{u} : ∀ {D : Type u} [inst : TopologicalSpace.{u} D] [@T0Space.{u} D inst],
  Iff (@InjectiveSpace.{u, u} D inst)
    (∃ (E : Type u) (inst_2 : CompleteLattice.{u} E),
      And (@DomainTheory.ContinuousLattice.{u} E inst_2)
        (Nonempty.{u + 1}
          (@Homeomorph.{u, u} D E inst (@DomainTheory.ContinuousLattice.scottTopologicalSpace.{u} E inst_2)))) :=
  @DomainTheory.ContinuousLattice.theorem_2_12.{u}

end DomainTheory.ContinuousLattice
