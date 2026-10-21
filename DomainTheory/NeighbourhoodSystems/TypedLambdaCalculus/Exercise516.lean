/-ai
For bits ε and δ and elements x and y of C, merging the pair of ε consed onto x and δ consed onto y equals ε consed onto δ consed onto the merge of the pair (x, y). For every element x of C, merging x with itself equals the doubling map of Example 4.4 applied to x. The composition of negation with itself is the identity approximable map on C. For every element x of C, negating twice returns x. Negation after cons of false equals cons of true after negation, as approximable maps: negating a string headed by 0 heads the negated string by 1. Negation after cons of true equals cons of false after negation, as approximable maps: negating a string headed by 1 heads the negated string by 0.

The numbered name example_516 is the conjunction of these statements. The proof is that conjunction.
ai-/
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
