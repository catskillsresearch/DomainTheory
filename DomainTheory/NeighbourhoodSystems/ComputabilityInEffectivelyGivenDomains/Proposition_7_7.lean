module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.dsharpEffective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition77
set_option linter.unusedVariables false
open NeighborhoodSystem Domain.Recursive IndefProduct

/-- Scott's Proposition 7.7: D♯ is effectively given. -/
theorem proposition_77 :
    ∀ {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)
      (hD : ∀ X, D.mem X → X.Nonempty),
      (Dsharp D hD).IsEffectivelyGiven :=
  @dsharp_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems.Proposition77
