/-ai
If D has a computable presentation and every neighbourhood of D is nonempty, then the sharp system is effectively given.

The numbered name theorem_77 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.dsharp_isEffectivelyGiven

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition77

set_option linter.unusedVariables false

theorem theorem_77.{u_1} : ∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D)
  (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven (Prod (List Bool) α)
    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD) :=
  @DomainTheory.NeighbourhoodSystems.Proposition77.dsharp_isEffectivelyGiven

end DomainTheory.NeighbourhoodSystems.Proposition77
