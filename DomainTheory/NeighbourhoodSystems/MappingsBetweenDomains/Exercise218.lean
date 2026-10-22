module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.hMap_not_surjective
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kMap_comp_hMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise218.kMap_not_injective

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise218

set_option linter.unusedVariables false

theorem example_218 : And
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap))) :=
  @And.intro
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap)))
  (@And.intro
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B))
    DomainTheory.NeighbourhoodSystems.Exercise218.hMap_not_surjective
    DomainTheory.NeighbourhoodSystems.Exercise218.kMap_comp_hMap)
  DomainTheory.NeighbourhoodSystems.Exercise218.kMap_not_injective

end DomainTheory.NeighbourhoodSystems.Exercise218
