module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.sigmaMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise216

/-- Scott's Exercise 2.16: the parity map is uniquely determined by its three equations, and
prefixing by a fixed string is the elementwise action of an approximable map. -/
theorem example_216 :
    (∀ {g : ApproximableMap ExampleB.B Example23.T},
      SatisfiesParityEquations g → g = Example23.parityMap) ∧
    (∀ (σ : ExampleB.Str) (x : ExampleB.B.Element),
      (sigmaMap σ).toElementMap x = ExampleB.sigmaElt σ x) :=
  ⟨@eq_parityMap_of_satisfies, toElementMap_sigmaMap⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
