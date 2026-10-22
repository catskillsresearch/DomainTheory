module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.pairSharp_isComputable
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise717.proj1_isComputable

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Proposition77

set_option linter.unusedVariables false

theorem example_717.{u_1} : And
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum (Prod (List Bool) α) (Prod (List Bool) α))
      (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.prod (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD))
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD))
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Prod (List Bool) α) (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.proj1Map α D hD)) :=
  @And.intro
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum (Prod (List Bool) α) (Prod (List Bool) α))
      (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.prod (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD))
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD))
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Prod (List Bool) α) (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.proj1Map α D hD))
  @DomainTheory.NeighbourhoodSystems.Proposition77.pairSharp_isComputable
  @DomainTheory.NeighbourhoodSystems.Proposition77.proj1_isComputable

end DomainTheory.NeighbourhoodSystems.Proposition77
