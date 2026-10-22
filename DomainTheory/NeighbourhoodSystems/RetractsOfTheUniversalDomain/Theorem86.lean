module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.sub_eq_self_iff_isFinitaryProjection
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86.isFinitaryProjection_subApprox

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem theorem_86.{u} : And
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)) :=
  @And.intro
  (And
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E)
        (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E)))
  (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
    @DomainTheory.NeighbourhoodSystems.FinitaryProjection (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
      (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
  (@And.intro
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E},
      Iff
        (@Eq (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E) (@DomainTheory.NeighbourhoodSystems.sub α E f)
          f)
        (@DomainTheory.NeighbourhoodSystems.FinitaryProjection α E f))
    (∀ {α : Type u} {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α},
      @DomainTheory.NeighbourhoodSystems.IsFinitary (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α E E)
        (@DomainTheory.NeighbourhoodSystems.funSpace α α E E) (@DomainTheory.NeighbourhoodSystems.Sub8_6.subApprox α E))
    @DomainTheory.NeighbourhoodSystems.sub_eq_self_iff_isFinitaryProjection
    @DomainTheory.NeighbourhoodSystems.Sub8_6.isFinitary_subApprox)
  @DomainTheory.NeighbourhoodSystems.Sub8_6.isFinitaryProjection_subApprox

end DomainTheory.NeighbourhoodSystems
