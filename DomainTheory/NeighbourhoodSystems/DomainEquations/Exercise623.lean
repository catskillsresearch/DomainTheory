/-ai
The evaluation map lies below the underlying map of every algebra homomorphism from Exp.

The numbered name example_623 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_le_algHom

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_623 : ∀ {N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys}
  (hN :
    @Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
  (B :
    @DomainTheory.NeighbourhoodSystems.TAlgebra DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N))
  (g :
    @DomainTheory.NeighbourhoodSystems.AlgHom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
      DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
      (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
      (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B),
  @LE.le
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
      (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
          DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
          (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
    (@Preorder.toLE
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (@PartialOrder.toPreorder
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
        (@DomainTheory.NeighbourhoodSystems.instPartialOrderApproximableMap
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.Exp N hN).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)))
    (@DomainTheory.NeighbourhoodSystems.Exercise619.descMap N hN B)
    (@Subtype.val
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
            (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
        (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
            DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
            (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys)
      (fun
          (f :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
                  (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
              (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier
                  DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
                  DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
                  (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys) =>
        @DomainTheory.NeighbourhoodSystems.Exercise510.IsStrict DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
              (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN)).sys
          (@DomainTheory.NeighbourhoodSystems.TAlgebra.carrier DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
              DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
              (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N) B).sys
          f)
      (@DomainTheory.NeighbourhoodSystems.AlgHom.hom DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys
        DomainTheory.NeighbourhoodSystems.Exercise619.instCategoryScottSys
        (DomainTheory.NeighbourhoodSystems.Exercise619.TexpF N)
        (DomainTheory.NeighbourhoodSystems.Exercise619.ExpAlg N hN) B g)) :=
  @DomainTheory.NeighbourhoodSystems.Exercise619.descMap_le_algHom

end DomainTheory.NeighbourhoodSystems.Exercise619
