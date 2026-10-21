/-ai
The while-loop satisfies the recursion w(x) = cond(p(x), w(f(x)), x).

The numbered name example_512 is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise512.whileMap_rec

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise512

set_option linter.unusedVariables false

theorem example_512.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (p :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap α DomainTheory.NeighbourhoodSystems.Example12.Token V
      DomainTheory.NeighbourhoodSystems.Exercise326.TD)
  (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α V V)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
      (@DomainTheory.NeighbourhoodSystems.Exercise512.whileMap α V p f) x)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
      (Sum DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)) α
      (@DomainTheory.NeighbourhoodSystems.prod DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
        DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V))
      V (@DomainTheory.NeighbourhoodSystems.Exercise326.cond α V)
      (@DomainTheory.NeighbourhoodSystems.pair DomainTheory.NeighbourhoodSystems.Example12.Token (Sum α α)
        DomainTheory.NeighbourhoodSystems.Exercise326.TD (@DomainTheory.NeighbourhoodSystems.prod α α V V)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α
          DomainTheory.NeighbourhoodSystems.Example12.Token V DomainTheory.NeighbourhoodSystems.Exercise326.TD p x)
        (@DomainTheory.NeighbourhoodSystems.pair α α V V
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V
            (@DomainTheory.NeighbourhoodSystems.Exercise512.whileMap α V p f)
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α α V V f x))
          x))) :=
  @DomainTheory.NeighbourhoodSystems.Exercise512.whileMap_rec

end DomainTheory.NeighbourhoodSystems.Exercise512
