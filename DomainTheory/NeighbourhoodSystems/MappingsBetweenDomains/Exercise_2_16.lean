module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.sigmaMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise216

/-- Scott's Exercise 2.16: the parity map is uniquely determined by its three equations, and
prefixing by a fixed string is the elementwise action of an approximable map. -/
theorem example_216 :
    (∀ {g : ApproximableMap BitDom.B Truth.T},
      SatisfiesParityEquations g → g = Truth.parityMap) ∧
    (∀ (σ : BitDom.Str) (x : BitDom.B.Element),
      (sigmaMap σ).toElementMap x = BitDom.sigmaElt σ x) :=
  ⟨@eq_parityMap_of_satisfies, toElementMap_sigmaMap⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
