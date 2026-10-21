/-ai
For positive n, Scott's domain A over {0,1}* is isomorphic to the separated sum of two copies of its n-fold cartesian power. A non-bottom element of A is a left or right copy of an n-tuple of elements of A.

The isomorphism is aaEquiv.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62A.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Example62A

open NeighborhoodSystem ApproximableMap ExampleB


variable {β : Type*} {n : ℕ}


variable {n : ℕ}


/-- **Example 6.2 (Scott 1981, PRG-19) — the domain equation `A ≅ Aⁿ + Aⁿ`.** Scott's "simple, yet
interesting generalization of `B`": the domain `A` over `{0,1}*` (whose non-`⊥` elements are the two
copies — left `−` and right `+` — of an `n`-tuple of elements of `A`) is isomorphic to the separated
sum `Aⁿ + Aⁿ` of two copies of its own `n`-fold cartesian power. -/
theorem A_domain_equation (hn : 0 < n) : Asys n hn ≅ᴰ AAsys hn := ⟨aaEquiv hn⟩

end Example62A
end DomainTheory.NeighbourhoodSystems
