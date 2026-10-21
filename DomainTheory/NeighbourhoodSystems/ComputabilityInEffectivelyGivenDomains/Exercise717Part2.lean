/-ai
If the target is effectively given and the two algebra maps are computable, then the universal strict map is a computable map from the sharp presentation into the presentation of the target.

The numbered name example_717_part2 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717Part2.gMap_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise717

set_option linter.unusedVariables false

theorem example_717_part2.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {u : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E}
  {v :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β E E) E}
  (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D)
  (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β E),
  @DomainTheory.NeighbourhoodSystems.IsComputableMap α β D E P Q u →
    @DomainTheory.NeighbourhoodSystems.IsComputableMap (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β E E) E
        (@DomainTheory.NeighbourhoodSystems.prodPresentation β β E E Q Q) Q v →
      @DomainTheory.NeighbourhoodSystems.IsComputableMap (Prod (List Bool) α) β
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD) E
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD) Q
        (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α β D E u v hD) :=
  @DomainTheory.NeighbourhoodSystems.Exercise717.gMap_isComputable

end DomainTheory.NeighbourhoodSystems.Exercise717
