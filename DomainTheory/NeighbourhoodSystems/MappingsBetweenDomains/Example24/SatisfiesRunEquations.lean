/-ai
An approximable self-map of the binary system satisfies the run equations when prepending a zero commutes with the map, prepending two ones leaves the value unchanged, prepending one and then zero emits a zero and then the input, for every element, and the map sends the principal element of a single one to bottom.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The four equations of Exercise 2.17.** `g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x` for
*every* `x : |B|`, plus the single value equation `g(1) = ⊥` (this last one is *not* quantified
over `x`: it pins down `g` at the single finite element `1⊥`, matching Scott's literal statement
"`g(1) = ⊥`"). -/
structure SatisfiesRunEquations (g : ApproximableMap B B) : Prop where
  zero : ∀ x : B.Element, g.toElementMap (sigmaElt [false] x) = sigmaElt [false] (g.toElementMap x)
  oneOne : ∀ x : B.Element, g.toElementMap (sigmaElt [true, true] x) = g.toElementMap (sigmaElt [true] x)
  oneZero : ∀ x : B.Element, g.toElementMap (sigmaElt [true, false] x) = sigmaElt [false] x
  one : g.toElementMap (sigmaElt [true] B.bot) = B.bot

end DomainTheory.NeighbourhoodSystems.Example24
