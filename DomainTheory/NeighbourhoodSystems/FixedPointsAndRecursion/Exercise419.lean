module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.peano_nil_ne_cons
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.one_def_strBot
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.one_def_strElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.peano_cons_disjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.peano_cons_injective
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.peano_induction

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise419

set_option linter.unusedVariables false

theorem example_419 : And
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ))
  (∀ (P : DomainTheory.NeighbourhoodSystems.ExampleB.Str → Prop),
    P (@List.nil Bool) →
      (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ → P (@List.cons Bool b σ)) →
        ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str), P σ)
  (@And.intro
    (And
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ)))
    (∀ {b : Bool} {σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str},
      @Eq (List Bool) (@List.cons Bool b σ) (@List.cons Bool b τ) →
        @Eq DomainTheory.NeighbourhoodSystems.ExampleB.Str σ τ)
    (@And.intro
      (And
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))))
      (∀ (σ τ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        @Ne (List Bool) (@List.cons Bool Bool.false σ) (@List.cons Bool Bool.true τ))
      (@And.intro
        (And
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))))
        (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
          @Eq
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
              DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ))
            (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
              (DomainTheory.NeighbourhoodSystems.Example44.strElem σ)))
        (@And.intro
          (∀ (b : Bool) (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Ne (List Bool) (@List.nil Bool) (@List.cons Bool b σ))
          (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.Exercise419.T)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example12.Token
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise419.T
                DomainTheory.NeighbourhoodSystems.Exercise419.oneMap
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ))
              (DomainTheory.NeighbourhoodSystems.Exercise419.oneDef
                (DomainTheory.NeighbourhoodSystems.Example44.strBot σ)))
          DomainTheory.NeighbourhoodSystems.Exercise419.peano_nil_ne_cons
          DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strBot)
        DomainTheory.NeighbourhoodSystems.Exercise419.one_def_strElem)
      DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_disjoint)
    @DomainTheory.NeighbourhoodSystems.Exercise419.peano_cons_injective)
  DomainTheory.NeighbourhoodSystems.Exercise419.peano_induction

end DomainTheory.NeighbourhoodSystems.Exercise419
