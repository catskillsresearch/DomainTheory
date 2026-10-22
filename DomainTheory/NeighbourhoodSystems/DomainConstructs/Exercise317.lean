module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.fg_le_id
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise317.gf_eq_id

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise317

set_option linter.unusedVariables false

theorem example_317 : And
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B)) :=
  @And.intro
  (@LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T))
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T)
        (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
          DomainTheory.NeighbourhoodSystems.Exercise317.T))
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T)
          (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
            DomainTheory.NeighbourhoodSystems.Exercise317.T))))
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.Exercise317.f DomainTheory.NeighbourhoodSystems.Exercise317.g)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token)
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)))
  (@Eq
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
      DomainTheory.NeighbourhoodSystems.ExampleB.B)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
      (Prod Nat DomainTheory.NeighbourhoodSystems.Example12.Token) DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B
      (@DomainTheory.NeighbourhoodSystems.iterSys DomainTheory.NeighbourhoodSystems.Example12.Token
        DomainTheory.NeighbourhoodSystems.Exercise317.T)
      DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise317.g
      DomainTheory.NeighbourhoodSystems.Exercise317.f)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.B))
  DomainTheory.NeighbourhoodSystems.Exercise317.fg_le_id DomainTheory.NeighbourhoodSystems.Exercise317.gf_eq_id

end DomainTheory.NeighbourhoodSystems.Exercise317
