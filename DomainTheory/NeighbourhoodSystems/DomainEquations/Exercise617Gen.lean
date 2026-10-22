module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617Gen.Cn_domain_equation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise617Gen

set_option linter.unusedVariables false

theorem example_617_gen : ∀ (A : Type) [inst : DecidableEq A] [Inhabited A],
  @DomainTheory.NeighbourhoodSystems.Isomorphic (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A)
    (DomainTheory.NeighbourhoodSystems.Exercise617Gen.SigTok A
      (DomainTheory.NeighbourhoodSystems.Exercise617Gen.Strn A))
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn A inst)
    (@DomainTheory.NeighbourhoodSystems.Exercise617Gen.CCn A inst) :=
  DomainTheory.NeighbourhoodSystems.Exercise617Gen.Cn_domain_equation

end DomainTheory.NeighbourhoodSystems.Exercise617Gen
