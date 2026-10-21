/-ai
Every element of the lift is either the fresh bottom or the lift of some element of the original system. The coalesced sum of the lifts of D and E is domain-isomorphic to the separated sum of D and E. The smash product of the lifts of D and E is domain-isomorphic to the lift of the product of D and E.

The numbered name example_626 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.eq_liftBot_or_exists_liftUp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift_oplus_lift_iso_sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise626.lift_otimes_lift_iso_lift_prod

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_626 : And
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys) :=
  @And.intro
  (And
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys))
  (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
    @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.otimes E.lift).sys (D.prod E).lift.sys)
  (@And.intro
    (∀ {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      {hD :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
      (z :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD)),
      Or
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
          z (DomainTheory.NeighbourhoodSystems.Exercise619.liftBot D hD))
        (∃ (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            D),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.liftTok D hD))
            z (@DomainTheory.NeighbourhoodSystems.Exercise619.liftUp D hD x)))
    (∀ {D E : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys},
      @DomainTheory.NeighbourhoodSystems.Isomorphic DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (D.lift.oplus E.lift).sys (D.sum E).sys)
    @DomainTheory.NeighbourhoodSystems.Exercise619.eq_liftBot_or_exists_liftUp
    @DomainTheory.NeighbourhoodSystems.Exercise619.lift_oplus_lift_iso_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise619.lift_otimes_lift_iso_lift_prod

end DomainTheory.NeighbourhoodSystems.Exercise619
