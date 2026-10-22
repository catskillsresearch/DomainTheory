module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_succ_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tElt_unfold

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

set_option linter.unusedVariables false

theorem example_516_thue_morse : And
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
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
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  @And.intro
  (∀ (k : Nat),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.iterElem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Exercise516.tmOp
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (DomainTheory.NeighbourhoodSystems.Example44.strBot
        (@Nat.iterate DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Exercise516.expand k (@List.cons Bool Bool.false (@List.nil Bool)))))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Example44.C)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C
      DomainTheory.NeighbourhoodSystems.Example44.C (DomainTheory.NeighbourhoodSystems.Example44.consMap Bool.false)
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
            DomainTheory.NeighbourhoodSystems.Exercise516.negMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C DomainTheory.NeighbourhoodSystems.Example44.C
            DomainTheory.NeighbourhoodSystems.Exercise516.tailMap DomainTheory.NeighbourhoodSystems.Exercise516.tElt))))
    DomainTheory.NeighbourhoodSystems.Exercise516.tElt)
  DomainTheory.NeighbourhoodSystems.Exercise516.iterElem_succ_eq
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_unfold

end DomainTheory.NeighbourhoodSystems.Exercise516
