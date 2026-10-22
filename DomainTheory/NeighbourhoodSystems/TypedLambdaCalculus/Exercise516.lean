module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_diag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_comp_negMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_negMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_cons_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_cons_true

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

set_option linter.unusedVariables false

theorem example_516 : And
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap)) :=
  @And.intro
  (And
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
      (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
  (@And.intro
    (And
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
        (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false))
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
        DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.true)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap))
    (@And.intro
      (And
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)))
      (∀
        (x :
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C),
        @Eq
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
              DomainTheory.NeighbourhoodSystems.Exercise516.negMap x))
          x)
      (@And.intro
        (And
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x)))
        (@Eq
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.negMap
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C))
        (@And.intro
          (∀ (ε δ : Bool)
            (x y :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap ε) x)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                    (DomainTheory.NeighbourhoodSystems.Example44.consMap δ) y)))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                (DomainTheory.NeighbourhoodSystems.Example44.consMap ε)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                  (DomainTheory.NeighbourhoodSystems.Example44.consMap δ)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                    (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                    DomainTheory.NeighbourhoodSystems.ExampleB.Str
                    (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C)
                    DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                    (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                      DomainTheory.NeighbourhoodSystems.Example44.C x y)))))
          (∀
            (x :
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                (Sum DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str)
                DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C)
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap
                (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.ExampleB.Str
                  DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
                  DomainTheory.NeighbourhoodSystems.Example44.C x x))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
                DomainTheory.NeighbourhoodSystems.Exercise516.dMap x))
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_cons
          DomainTheory.NeighbourhoodSystems.Exercise516.mergeMap_diag)
        DomainTheory.NeighbourhoodSystems.Exercise516.negMap_comp_negMap)
      DomainTheory.NeighbourhoodSystems.Exercise516.negMap_negMap)
    DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_false)
  DomainTheory.NeighbourhoodSystems.Exercise516.neg_cons_true

end DomainTheory.NeighbourhoodSystems.Exercise516
