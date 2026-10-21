/-ai
If the point filters of two reals agree, then the reals are equal. The intersection of two rational-interval neighbourhoods with a point in common is again a rational-interval neighbourhood.

The numbered name example_117 is the conjunction of these statements. The proof is that conjunction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.filterAt_injective
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.inter_mem'

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.RatInterval

set_option linter.unusedVariables false

theorem example_117 : And
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y)) :=
  @And.intro
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y))
  @DomainTheory.NeighbourhoodSystems.RatInterval.filterAt_injective
  @DomainTheory.NeighbourhoodSystems.RatInterval.inter_mem'

end DomainTheory.NeighbourhoodSystems.RatInterval
