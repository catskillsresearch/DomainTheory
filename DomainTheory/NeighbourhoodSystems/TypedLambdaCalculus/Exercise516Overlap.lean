/-ai
The element t is cube-free in Scott's form: for a finite string u and a nonempty finite string a, the partial element of u followed by three copies of a does not lie below t.

The numbered name example_516_overlap is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.tElt_cube_free

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

set_option linter.unusedVariables false

theorem example_516_overlap : ∀ (u a : DomainTheory.NeighbourhoodSystems.ExampleB.Str),
  @Ne DomainTheory.NeighbourhoodSystems.ExampleB.Str a (@List.nil Bool) →
    Not
      (@LE.le
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example44.C)
        (@Preorder.toLE
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.Example44.C)
          (@PartialOrder.toPreorder
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Example44.C)))
        (DomainTheory.NeighbourhoodSystems.Example44.strBot
          (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
            (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
            (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
              DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
              (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool))
              (@HAppend.hAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str
                DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
                (@instHAppendOfAppend DomainTheory.NeighbourhoodSystems.ExampleB.Str (@List.instAppend Bool)) u a)
              a)
            a))
        DomainTheory.NeighbourhoodSystems.Exercise516.tElt) :=
  DomainTheory.NeighbourhoodSystems.Exercise516.tElt_cube_free

end DomainTheory.NeighbourhoodSystems.Exercise516
