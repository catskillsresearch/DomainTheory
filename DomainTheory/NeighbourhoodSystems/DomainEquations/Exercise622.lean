/-ai
The solution of the vertical-naturals equation is itself a rooted domain, so the stream equation has a solution over that very domain.

The numbered name example_622 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStar_over_N_exists

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_622 : ∃ (N : DomainTheory.NeighbourhoodSystems.Exercise619.ScottSys),
  And
    (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.master DomainTheory.NeighbourhoodSystems.ExampleB.Str
        N.sys)
      (@List.nil Bool))
    (∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
      @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
      @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
        ((DomainTheory.NeighbourhoodSystems.Exercise619.NStarExpr N).obj
            (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys) :=
  DomainTheory.NeighbourhoodSystems.Exercise619.NStar_over_N_exists

end DomainTheory.NeighbourhoodSystems.Exercise619
