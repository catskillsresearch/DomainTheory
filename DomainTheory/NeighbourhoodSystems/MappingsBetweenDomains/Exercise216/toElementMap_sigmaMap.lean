/-ai
The element map of the prefixing map of a finite string is Scott's prefixing operation on elements.

Two elements are equal when they contain the same neighbourhoods. A neighbourhood of the element map consists of an input neighbourhood of the element, an output neighbourhood, and a prefixed inclusion, and dropping the containment in the element leaves a neighbourhood of the prefixed element. The converse reassembles the same data, using that the input neighbourhood belongs to the element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise216.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Exercise 2.16.** The elementwise action of `sigmaMap σ` is Scott's `σx`: `(sigmaMap σ)(x) =
σx` for every `x ∈ |B|`. -/
theorem toElementMap_sigmaMap (σ : Str) (x : B.Element) :
    (sigmaMap σ).toElementMap x = sigmaElt σ x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hxX, _, hY, hsub⟩
    exact ⟨hY, X, hxX, hsub⟩
  · rintro ⟨hY, X, hxX, hsub⟩
    exact ⟨X, hxX, x.sub hxX, hY, hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
