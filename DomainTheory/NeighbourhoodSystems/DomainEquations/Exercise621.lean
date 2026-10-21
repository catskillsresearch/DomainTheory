/-ai
For every expression T and every nonempty set Γ of strings, the token-level recursion gFun T Γ equals the master of T applied to the singleton system on Γ.

The numbered name example_621 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise619

set_option linter.unusedVariables false

theorem example_621 : And
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
        @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
        @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
          (T.obj (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys)
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str) Γ (@List.nil Bool))
          (@Eq (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.Exercise619.gFun T Γ) Γ)) :=
  @And.intro
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str) (h :
        @Set.Nonempty DomainTheory.NeighbourhoodSystems.ExampleB.Str Γ),
        @DomainTheory.NeighbourhoodSystems.Subsystem DomainTheory.NeighbourhoodSystems.ExampleB.Str
          (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h).sys
          (T.obj (DomainTheory.NeighbourhoodSystems.Exercise619.singletonSys Γ h)).sys)
  (∀ (T : DomainTheory.NeighbourhoodSystems.Exercise619.GExpr),
    T.RootedConst →
      ∃ (Γ : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@Membership.mem (List Bool) (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instMembership DomainTheory.NeighbourhoodSystems.ExampleB.Str) Γ (@List.nil Bool))
          (@Eq (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.Exercise619.gFun T Γ) Γ))
  DomainTheory.NeighbourhoodSystems.Exercise619.gExists_singleton_subsystem
  DomainTheory.NeighbourhoodSystems.Exercise619.gExists_tok_fixedPoint

end DomainTheory.NeighbourhoodSystems.Exercise619
