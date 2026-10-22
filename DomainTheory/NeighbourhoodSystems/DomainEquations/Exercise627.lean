module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.otimes_trianglelefteq_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.fst_trianglelefteq_prod
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.not_trianglelefteq_otimes
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.oplus_trianglelefteq_sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise627.strictFun_trianglelefteq_funSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise627

set_option linter.unusedVariables false

theorem example_627.{u_1, u_2} : And
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁)))
  (∀ {α : Type u_1} {β : Type u_2} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β),
    @DomainTheory.NeighbourhoodSystems.Trianglelefteq
      (@DomainTheory.NeighbourhoodSystems.Exercise510.StrictMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.Exercise510.strictFun α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
  (@And.intro
    (And
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt))))
    (∀ {D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
      (h₀ :
        ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              X →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X)
      (h₁ :
        ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str D₁
              Y →
            @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y),
      @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)
        (DomainTheory.NeighbourhoodSystems.Exercise619.sumTok D₀ D₁ h₀ h₁))
    (@And.intro
      (And
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁)))
      (Not
        (@DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
          (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok DomainTheory.NeighbourhoodSystems.Exercise627.twoPt
            DomainTheory.NeighbourhoodSystems.Exercise627.unitPt)))
      (@And.intro
        (And
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁)))
        (∀
          (D₀ D₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
            (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
        (@And.intro
          (∀
            (D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (DomainTheory.NeighbourhoodSystems.Exercise619.otimesTok D₀ D₁)
              (DomainTheory.NeighbourhoodSystems.Exercise619.prodTok D₀ D₁))
          (∀
            {D₀ D₁ :
              DomainTheory.NeighbourhoodSystems.NeighborhoodSystem DomainTheory.NeighbourhoodSystems.ExampleB.Str}
            {h₀ :
              ∀ (X : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₀ X →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str X}
            {h₁ :
              ∀ (Y : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    D₁ Y →
                  @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Y},
            @DomainTheory.NeighbourhoodSystems.Trianglelefteq DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str D₀
              (DomainTheory.NeighbourhoodSystems.Exercise619.oplusTok D₀ D₁ h₀ h₁))
          DomainTheory.NeighbourhoodSystems.Exercise627.otimes_trianglelefteq_prod
          @DomainTheory.NeighbourhoodSystems.Exercise627.inl_trianglelefteq_oplus)
        DomainTheory.NeighbourhoodSystems.Exercise627.fst_trianglelefteq_prod)
      DomainTheory.NeighbourhoodSystems.Exercise627.not_trianglelefteq_otimes)
    @DomainTheory.NeighbourhoodSystems.Exercise627.oplus_trianglelefteq_sum)
  @DomainTheory.NeighbourhoodSystems.Exercise627.strictFun_trianglelefteq_funSpace

end DomainTheory.NeighbourhoodSystems.Exercise627
