/-ai
SatisfiesParityEquations records that an approximable map from the binary-string domain into the truth-value domain sends every string with a leading one to true, every string with a leading zero followed by one to false, and every string with a leading pair of zeros to the value of the remaining string.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The three equations of Exercise 2.16.** `f(1x) = true`, `f(01x) = false`, `f(00x) = f(x)`,
for *every* `x : |B|`. -/
structure SatisfiesParityEquations (g : ApproximableMap B Example23.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Example23.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Example23.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x

end DomainTheory.NeighbourhoodSystems.Exercise216
