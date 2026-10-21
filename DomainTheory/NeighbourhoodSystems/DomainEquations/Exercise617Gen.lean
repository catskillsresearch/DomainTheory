/-ai
The generic sequence domain over a decidable inhabited alphabet is isomorphic, as a domain, to the unit summed with one copy of itself for each letter.

The numbered name example_617_gen is that statement.
ai-/
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
