module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_2

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Examples_8_4

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise_8_15

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open Domain.Recursive NeighborhoodSystem
open NeighborhoodSystem ApproximableMap
section
universe u
variable {α : Type u} {E : NeighborhoodSystem α}
/- concordance: source L5163 EXERCISE 8.16 order of projections -/
/-- **Exercise 8.16 (Scott 1981, PRG-19), in full.**

Part 1: for finitary projections `a, b : E → E`, `a ≤ b ↔ D_a ◁ D_b` (fills the gap at the end of
Theorem 8.6's proof).

Part 2: if `a : E → E` is computable relative to a `ComputablePresentation P` of `E` — i.e. `E` is
effectively given (via `P`) and `a` is computable (relative to `P`) — then `D_a` is effectively
given (finishes off Theorem 8.8's proof). This is `Theorem88m.lean`'s `fixedNbhd_isEffectivelyGiven`,
cited here under the exercise's name. -/
theorem exercise_8_16 :
    (∀ {a b : ApproximableMap E E}, FinitaryProjection a → FinitaryProjection b →
        (a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b)) ∧
      (∀ {P : ComputablePresentation E} {a : ApproximableMap E E},
        ComputableMap P P a → (fixedNbhd a).IsEffectivelyGiven) :=
  ⟨fun ha hb => isFinitaryProjection_le_iff_fixedNbhd_subsystem ha hb,
    fun hcomp => fixedNbhd_isEffectivelyGiven hcomp⟩
end

section
set_option linter.unusedVariables false

theorem example_816.{u} : And
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    And
      (∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            Iff
              (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                a b)
              (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
      (∀ {P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E}
        {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α α E E P P a →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
        Iff
          (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
            a b)
          (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b))) :=
  @And.intro
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    And
      (∀ {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
            Iff
              (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                  (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                    (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
                a b)
              (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
                (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
      (∀ {P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α E}
        {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α α E E P P a →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {a b : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E a →
      @DomainTheory.NeighbourhoodSystems.FinitaryProjection α E b →
        Iff
          (@LE.le (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
                (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap α α E E)))
            a b)
          (@DomainTheory.NeighbourhoodSystems.Subsystem α (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E a)
            (@DomainTheory.NeighbourhoodSystems.fixedNbhd α E b)))
  @DomainTheory.NeighbourhoodSystems.exercise_8_16
  @DomainTheory.NeighbourhoodSystems.isFinitaryProjection_le_iff_fixedNbhd_subsystem
end

end DomainTheory.NeighbourhoodSystems
end

